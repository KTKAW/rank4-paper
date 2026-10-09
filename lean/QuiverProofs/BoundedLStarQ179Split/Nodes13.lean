import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable52 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 52).word) (BoundedLStarData.q179.node 52) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,3]) (ofSix (38) (-9) (1) (0) (5) (-1))
  rw [q179_prefix52]
  intro u v; rfl

theorem q179_cyclic52 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 52) := by decide +kernel

theorem q179_edge52_0 :
    EdgeChecks BoundedLStarData.q179 52 0 ((BoundedLStarData.q179.core 52).edges 0) := by decide +kernel

theorem q179_edge52_1 :
    EdgeChecks BoundedLStarData.q179 52 1 ((BoundedLStarData.q179.core 52).edges 1) := by decide +kernel

theorem q179_edge52_2 :
    EdgeChecks BoundedLStarData.q179 52 2 ((BoundedLStarData.q179.core 52).edges 2) := by decide +kernel

theorem q179_edge52_3 :
    EdgeChecks BoundedLStarData.q179 52 3 ((BoundedLStarData.q179.core 52).edges 3) := by decide +kernel

theorem q179_triangles52 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 52) = true := by decide +kernel

theorem q179_descent52 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 52) = true := by
  change allTriangleDescentsCheck (ofSix (38) (-9) (1) (0) (5) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable53 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 53).word) (BoundedLStarData.q179.node 53) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,2,3,0]) (ofSix (8) (1) (-3) (-5) (24) (2))
  rw [q179_prefix53]
  intro u v; rfl

theorem q179_cyclic53 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 53) := by decide +kernel

theorem q179_edge53_0 :
    EdgeChecks BoundedLStarData.q179 53 0 ((BoundedLStarData.q179.core 53).edges 0) := by decide +kernel

theorem q179_edge53_1 :
    EdgeChecks BoundedLStarData.q179 53 1 ((BoundedLStarData.q179.core 53).edges 1) := by decide +kernel

theorem q179_edge53_2 :
    EdgeChecks BoundedLStarData.q179 53 2 ((BoundedLStarData.q179.core 53).edges 2) := by decide +kernel

theorem q179_edge53_3 :
    EdgeChecks BoundedLStarData.q179 53 3 ((BoundedLStarData.q179.core 53).edges 3) := by decide +kernel

theorem q179_triangles53 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 53) = true := by decide +kernel

theorem q179_descent53 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 53) = true := by
  change allTriangleDescentsCheck (ofSix (8) (1) (-3) (-5) (24) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable54 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 54).word) (BoundedLStarData.q179.node 54) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,1]) (ofSix (6) (-52) (-7) (9) (1) (3))
  rw [q179_prefix54]
  intro u v; rfl

theorem q179_cyclic54 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 54) := by decide +kernel

theorem q179_edge54_0 :
    EdgeChecks BoundedLStarData.q179 54 0 ((BoundedLStarData.q179.core 54).edges 0) := by decide +kernel

theorem q179_edge54_1 :
    EdgeChecks BoundedLStarData.q179 54 1 ((BoundedLStarData.q179.core 54).edges 1) := by decide +kernel

theorem q179_edge54_2 :
    EdgeChecks BoundedLStarData.q179 54 2 ((BoundedLStarData.q179.core 54).edges 2) := by decide +kernel

theorem q179_edge54_3 :
    EdgeChecks BoundedLStarData.q179 54 3 ((BoundedLStarData.q179.core 54).edges 3) := by decide +kernel

theorem q179_triangles54 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 54) = true := by decide +kernel

theorem q179_descent54 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 54) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-52) (-7) (9) (1) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable55 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 55).word) (BoundedLStarData.q179.node 55) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,3]) (ofSix (-6) (-1) (1) (-12) (1) (-3))
  rw [q179_prefix55]
  intro u v; rfl

theorem q179_cyclic55 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 55) := by decide +kernel

theorem q179_edge55_0 :
    EdgeChecks BoundedLStarData.q179 55 0 ((BoundedLStarData.q179.core 55).edges 0) := by decide +kernel

theorem q179_edge55_1 :
    EdgeChecks BoundedLStarData.q179 55 1 ((BoundedLStarData.q179.core 55).edges 1) := by decide +kernel

theorem q179_edge55_2 :
    EdgeChecks BoundedLStarData.q179 55 2 ((BoundedLStarData.q179.core 55).edges 2) := by decide +kernel

theorem q179_edge55_3 :
    EdgeChecks BoundedLStarData.q179 55 3 ((BoundedLStarData.q179.core 55).edges 3) := by decide +kernel

theorem q179_triangles55 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 55) = true := by decide +kernel

theorem q179_descent55 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 55) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (-1) (1) (-12) (1) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
