import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable40 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 40).word) (BoundedLStarData.q179.node 40) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,0,2,1]) (ofSix (-6) (16) (1) (-3) (1) (-2))
  rw [q179_prefix40]
  intro u v; rfl

theorem q179_cyclic40 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 40) := by decide +kernel

theorem q179_edge40_0 :
    EdgeChecks BoundedLStarData.q179 40 0 ((BoundedLStarData.q179.core 40).edges 0) := by decide +kernel

theorem q179_edge40_1 :
    EdgeChecks BoundedLStarData.q179 40 1 ((BoundedLStarData.q179.core 40).edges 1) := by decide +kernel

theorem q179_edge40_2 :
    EdgeChecks BoundedLStarData.q179 40 2 ((BoundedLStarData.q179.core 40).edges 2) := by decide +kernel

theorem q179_edge40_3 :
    EdgeChecks BoundedLStarData.q179 40 3 ((BoundedLStarData.q179.core 40).edges 3) := by decide +kernel

theorem q179_triangles40 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 40) = true := by decide +kernel

theorem q179_descent40 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 40) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (16) (1) (-3) (1) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable41 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 41).word) (BoundedLStarData.q179.node 41) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,1,3,0]) (ofSix (0) (7) (-1) (-7) (2) (2))
  rw [q179_prefix41]
  intro u v; rfl

theorem q179_cyclic41 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 41) := by decide +kernel

theorem q179_edge41_0 :
    EdgeChecks BoundedLStarData.q179 41 0 ((BoundedLStarData.q179.core 41).edges 0) := by decide +kernel

theorem q179_edge41_1 :
    EdgeChecks BoundedLStarData.q179 41 1 ((BoundedLStarData.q179.core 41).edges 1) := by decide +kernel

theorem q179_edge41_2 :
    EdgeChecks BoundedLStarData.q179 41 2 ((BoundedLStarData.q179.core 41).edges 2) := by decide +kernel

theorem q179_edge41_3 :
    EdgeChecks BoundedLStarData.q179 41 3 ((BoundedLStarData.q179.core 41).edges 3) := by decide +kernel

theorem q179_triangles41 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 41) = true := by decide +kernel

theorem q179_descent41 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 41) = true := by
  change allTriangleDescentsCheck (ofSix (0) (7) (-1) (-7) (2) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable42 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 42).word) (BoundedLStarData.q179.node 42) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,2,0,1]) (ofSix (0) (-2) (3) (-3) (1) (-8))
  rw [q179_prefix42]
  intro u v; rfl

theorem q179_cyclic42 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 42) := by decide +kernel

theorem q179_edge42_0 :
    EdgeChecks BoundedLStarData.q179 42 0 ((BoundedLStarData.q179.core 42).edges 0) := by decide +kernel

theorem q179_edge42_1 :
    EdgeChecks BoundedLStarData.q179 42 1 ((BoundedLStarData.q179.core 42).edges 1) := by decide +kernel

theorem q179_edge42_2 :
    EdgeChecks BoundedLStarData.q179 42 2 ((BoundedLStarData.q179.core 42).edges 2) := by decide +kernel

theorem q179_edge42_3 :
    EdgeChecks BoundedLStarData.q179 42 3 ((BoundedLStarData.q179.core 42).edges 3) := by decide +kernel

theorem q179_triangles42 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 42) = true := by decide +kernel

theorem q179_descent42 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 42) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-2) (3) (-3) (1) (-8)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable43 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 43).word) (BoundedLStarData.q179.node 43) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [3,2,0,3]) (ofSix (3) (13) (-3) (3) (1) (5))
  rw [q179_prefix43]
  intro u v; rfl

theorem q179_cyclic43 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 43) := by decide +kernel

theorem q179_edge43_0 :
    EdgeChecks BoundedLStarData.q179 43 0 ((BoundedLStarData.q179.core 43).edges 0) := by decide +kernel

theorem q179_edge43_1 :
    EdgeChecks BoundedLStarData.q179 43 1 ((BoundedLStarData.q179.core 43).edges 1) := by decide +kernel

theorem q179_edge43_2 :
    EdgeChecks BoundedLStarData.q179 43 2 ((BoundedLStarData.q179.core 43).edges 2) := by decide +kernel

theorem q179_edge43_3 :
    EdgeChecks BoundedLStarData.q179 43 3 ((BoundedLStarData.q179.core 43).edges 3) := by decide +kernel

theorem q179_triangles43 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 43) = true := by decide +kernel

theorem q179_descent43 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 43) = true := by
  change allTriangleDescentsCheck (ofSix (3) (13) (-3) (3) (1) (5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
