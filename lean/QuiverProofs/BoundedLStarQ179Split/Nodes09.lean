import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable36 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 36).word) (BoundedLStarData.q179.node 36) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2]) (ofSix (38) (-8) (-1) (5) (-5) (1))
  rw [q179_prefix36]
  intro u v; rfl

theorem q179_cyclic36 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 36) := by decide +kernel

theorem q179_edge36_0 :
    EdgeChecks BoundedLStarData.q179 36 0 ((BoundedLStarData.q179.core 36).edges 0) := by decide +kernel

theorem q179_edge36_1 :
    EdgeChecks BoundedLStarData.q179 36 1 ((BoundedLStarData.q179.core 36).edges 1) := by decide +kernel

theorem q179_edge36_2 :
    EdgeChecks BoundedLStarData.q179 36 2 ((BoundedLStarData.q179.core 36).edges 2) := by decide +kernel

theorem q179_edge36_3 :
    EdgeChecks BoundedLStarData.q179 36 3 ((BoundedLStarData.q179.core 36).edges 3) := by decide +kernel

theorem q179_triangles36 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 36) = true := by decide +kernel

theorem q179_descent36 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 36) = true := by
  change allTriangleDescentsCheck (ofSix (38) (-8) (-1) (5) (-5) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable37 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 37).word) (BoundedLStarData.q179.node 37) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,2,3]) (ofSix (-8) (-1) (3) (-5) (0) (-1))
  rw [q179_prefix37]
  intro u v; rfl

theorem q179_cyclic37 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 37) := by decide +kernel

theorem q179_edge37_0 :
    EdgeChecks BoundedLStarData.q179 37 0 ((BoundedLStarData.q179.core 37).edges 0) := by decide +kernel

theorem q179_edge37_1 :
    EdgeChecks BoundedLStarData.q179 37 1 ((BoundedLStarData.q179.core 37).edges 1) := by decide +kernel

theorem q179_edge37_2 :
    EdgeChecks BoundedLStarData.q179 37 2 ((BoundedLStarData.q179.core 37).edges 2) := by decide +kernel

theorem q179_edge37_3 :
    EdgeChecks BoundedLStarData.q179 37 3 ((BoundedLStarData.q179.core 37).edges 3) := by decide +kernel

theorem q179_triangles37 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 37) = true := by decide +kernel

theorem q179_descent37 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 37) = true := by
  change allTriangleDescentsCheck (ofSix (-8) (-1) (3) (-5) (0) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable38 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 38).word) (BoundedLStarData.q179.node 38) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,1,3]) (ofSix (2) (2) (-1) (-7) (2) (-5))
  rw [q179_prefix38]
  intro u v; rfl

theorem q179_cyclic38 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 38) := by decide +kernel

theorem q179_edge38_0 :
    EdgeChecks BoundedLStarData.q179 38 0 ((BoundedLStarData.q179.core 38).edges 0) := by decide +kernel

theorem q179_edge38_1 :
    EdgeChecks BoundedLStarData.q179 38 1 ((BoundedLStarData.q179.core 38).edges 1) := by decide +kernel

theorem q179_edge38_2 :
    EdgeChecks BoundedLStarData.q179 38 2 ((BoundedLStarData.q179.core 38).edges 2) := by decide +kernel

theorem q179_edge38_3 :
    EdgeChecks BoundedLStarData.q179 38 3 ((BoundedLStarData.q179.core 38).edges 3) := by decide +kernel

theorem q179_triangles38 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 38) = true := by decide +kernel

theorem q179_descent38 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 38) = true := by
  change allTriangleDescentsCheck (ofSix (2) (2) (-1) (-7) (2) (-5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable39 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 39).word) (BoundedLStarData.q179.node 39) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,0]) (ofSix (-6) (2) (-1) (-9) (-1) (3))
  rw [q179_prefix39]
  intro u v; rfl

theorem q179_cyclic39 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 39) := by decide +kernel

theorem q179_edge39_0 :
    EdgeChecks BoundedLStarData.q179 39 0 ((BoundedLStarData.q179.core 39).edges 0) := by decide +kernel

theorem q179_edge39_1 :
    EdgeChecks BoundedLStarData.q179 39 1 ((BoundedLStarData.q179.core 39).edges 1) := by decide +kernel

theorem q179_edge39_2 :
    EdgeChecks BoundedLStarData.q179 39 2 ((BoundedLStarData.q179.core 39).edges 2) := by decide +kernel

theorem q179_edge39_3 :
    EdgeChecks BoundedLStarData.q179 39 3 ((BoundedLStarData.q179.core 39).edges 3) := by decide +kernel

theorem q179_triangles39 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 39) = true := by decide +kernel

theorem q179_descent39 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 39) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (2) (-1) (-9) (-1) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
