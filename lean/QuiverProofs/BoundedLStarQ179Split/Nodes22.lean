import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable88 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 88).word) (BoundedLStarData.q179.node 88) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,0,3,2]) (ofSix (86) (-1) (8) (-794) (7133) (-9))
  rw [q179_prefix91]
  intro u v; rfl

theorem q179_cyclic88 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 88) := by decide +kernel

theorem q179_edge88_0 :
    EdgeChecks BoundedLStarData.q179 88 0 ((BoundedLStarData.q179.core 88).edges 0) := by decide +kernel

theorem q179_edge88_1 :
    EdgeChecks BoundedLStarData.q179 88 1 ((BoundedLStarData.q179.core 88).edges 1) := by decide +kernel

theorem q179_edge88_2 :
    EdgeChecks BoundedLStarData.q179 88 2 ((BoundedLStarData.q179.core 88).edges 2) := by decide +kernel

theorem q179_edge88_3 :
    EdgeChecks BoundedLStarData.q179 88 3 ((BoundedLStarData.q179.core 88).edges 3) := by decide +kernel

theorem q179_triangles88 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 88) = true := by decide +kernel

theorem q179_descent88 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 88) = true := by
  change allTriangleDescentsCheck (ofSix (86) (-1) (8) (-794) (7133) (-9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
