import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable24 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 24).word) (BoundedLStarData.q179.node 24) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,2]) (ofSix (-8) (2) (-3) (-5) (0) (1))
  rw [q179_prefix24]
  intro u v; rfl

theorem q179_cyclic24 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 24) := by decide +kernel

theorem q179_edge24_0 :
    EdgeChecks BoundedLStarData.q179 24 0 ((BoundedLStarData.q179.core 24).edges 0) := by decide +kernel

theorem q179_edge24_1 :
    EdgeChecks BoundedLStarData.q179 24 1 ((BoundedLStarData.q179.core 24).edges 1) := by decide +kernel

theorem q179_edge24_2 :
    EdgeChecks BoundedLStarData.q179 24 2 ((BoundedLStarData.q179.core 24).edges 2) := by decide +kernel

theorem q179_edge24_3 :
    EdgeChecks BoundedLStarData.q179 24 3 ((BoundedLStarData.q179.core 24).edges 3) := by decide +kernel

theorem q179_triangles24 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 24) = true := by decide +kernel

theorem q179_descent24 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 24) = true := by
  change allTriangleDescentsCheck (ofSix (-8) (2) (-3) (-5) (0) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable25 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 25).word) (BoundedLStarData.q179.node 25) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,1]) (ofSix (0) (2) (1) (3) (-2) (5))
  rw [q179_prefix25]
  intro u v; rfl

theorem q179_cyclic25 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 25) := by decide +kernel

theorem q179_edge25_0 :
    EdgeChecks BoundedLStarData.q179 25 0 ((BoundedLStarData.q179.core 25).edges 0) := by decide +kernel

theorem q179_edge25_1 :
    EdgeChecks BoundedLStarData.q179 25 1 ((BoundedLStarData.q179.core 25).edges 1) := by decide +kernel

theorem q179_edge25_2 :
    EdgeChecks BoundedLStarData.q179 25 2 ((BoundedLStarData.q179.core 25).edges 2) := by decide +kernel

theorem q179_edge25_3 :
    EdgeChecks BoundedLStarData.q179 25 3 ((BoundedLStarData.q179.core 25).edges 3) := by decide +kernel

theorem q179_triangles25 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 25) = true := by decide +kernel

theorem q179_descent25 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 25) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (1) (3) (-2) (5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable26 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 26).word) (BoundedLStarData.q179.node 26) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2]) (ofSix (6) (-2) (1) (3) (-1) (1))
  rw [q179_prefix26]
  intro u v; rfl

theorem q179_cyclic26 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 26) := by decide +kernel

theorem q179_edge26_0 :
    EdgeChecks BoundedLStarData.q179 26 0 ((BoundedLStarData.q179.core 26).edges 0) := by decide +kernel

theorem q179_edge26_1 :
    EdgeChecks BoundedLStarData.q179 26 1 ((BoundedLStarData.q179.core 26).edges 1) := by decide +kernel

theorem q179_edge26_2 :
    EdgeChecks BoundedLStarData.q179 26 2 ((BoundedLStarData.q179.core 26).edges 2) := by decide +kernel

theorem q179_edge26_3 :
    EdgeChecks BoundedLStarData.q179 26 3 ((BoundedLStarData.q179.core 26).edges 3) := by decide +kernel

theorem q179_triangles26 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 26) = true := by decide +kernel

theorem q179_descent26 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 26) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-2) (1) (3) (-1) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable27 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 27).word) (BoundedLStarData.q179.node 27) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,1,3]) (ofSix (0) (-7) (1) (-7) (2) (-5))
  rw [q179_prefix27]
  intro u v; rfl

theorem q179_cyclic27 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 27) := by decide +kernel

theorem q179_edge27_0 :
    EdgeChecks BoundedLStarData.q179 27 0 ((BoundedLStarData.q179.core 27).edges 0) := by decide +kernel

theorem q179_edge27_1 :
    EdgeChecks BoundedLStarData.q179 27 1 ((BoundedLStarData.q179.core 27).edges 1) := by decide +kernel

theorem q179_edge27_2 :
    EdgeChecks BoundedLStarData.q179 27 2 ((BoundedLStarData.q179.core 27).edges 2) := by decide +kernel

theorem q179_edge27_3 :
    EdgeChecks BoundedLStarData.q179 27 3 ((BoundedLStarData.q179.core 27).edges 3) := by decide +kernel

theorem q179_triangles27 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 27) = true := by decide +kernel

theorem q179_descent27 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 27) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-7) (1) (-7) (2) (-5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
