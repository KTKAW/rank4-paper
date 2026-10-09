import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable60 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 60).word) (BoundedLStarData.q179.node 60) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2]) (ofSix (-86) (8) (-1) (-11) (13) (-1))
  rw [q179_prefix60]
  intro u v; rfl

theorem q179_cyclic60 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 60) := by decide +kernel

theorem q179_edge60_0 :
    EdgeChecks BoundedLStarData.q179 60 0 ((BoundedLStarData.q179.core 60).edges 0) := by decide +kernel

theorem q179_edge60_1 :
    EdgeChecks BoundedLStarData.q179 60 1 ((BoundedLStarData.q179.core 60).edges 1) := by decide +kernel

theorem q179_edge60_2 :
    EdgeChecks BoundedLStarData.q179 60 2 ((BoundedLStarData.q179.core 60).edges 2) := by decide +kernel

theorem q179_edge60_3 :
    EdgeChecks BoundedLStarData.q179 60 3 ((BoundedLStarData.q179.core 60).edges 3) := by decide +kernel

theorem q179_triangles60 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 60) = true := by decide +kernel

theorem q179_descent60 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 60) = true := by
  change allTriangleDescentsCheck (ofSix (-86) (8) (-1) (-11) (13) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable61 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 61).word) (BoundedLStarData.q179.node 61) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,2]) (ofSix (-14) (2) (-3) (-11) (13) (1))
  rw [q179_prefix61]
  intro u v; rfl

theorem q179_cyclic61 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 61) := by decide +kernel

theorem q179_edge61_0 :
    EdgeChecks BoundedLStarData.q179 61 0 ((BoundedLStarData.q179.core 61).edges 0) := by decide +kernel

theorem q179_edge61_1 :
    EdgeChecks BoundedLStarData.q179 61 1 ((BoundedLStarData.q179.core 61).edges 1) := by decide +kernel

theorem q179_edge61_2 :
    EdgeChecks BoundedLStarData.q179 61 2 ((BoundedLStarData.q179.core 61).edges 2) := by decide +kernel

theorem q179_edge61_3 :
    EdgeChecks BoundedLStarData.q179 61 3 ((BoundedLStarData.q179.core 61).edges 3) := by decide +kernel

theorem q179_triangles61 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 61) = true := by decide +kernel

theorem q179_descent61 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 61) = true := by
  change allTriangleDescentsCheck (ofSix (-14) (2) (-3) (-11) (13) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable62 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 62).word) (BoundedLStarData.q179.node 62) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,3]) (ofSix (-5) (-2) (1) (24) (-13) (1))
  rw [q179_prefix62]
  intro u v; rfl

theorem q179_cyclic62 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 62) := by decide +kernel

theorem q179_edge62_0 :
    EdgeChecks BoundedLStarData.q179 62 0 ((BoundedLStarData.q179.core 62).edges 0) := by decide +kernel

theorem q179_edge62_1 :
    EdgeChecks BoundedLStarData.q179 62 1 ((BoundedLStarData.q179.core 62).edges 1) := by decide +kernel

theorem q179_edge62_2 :
    EdgeChecks BoundedLStarData.q179 62 2 ((BoundedLStarData.q179.core 62).edges 2) := by decide +kernel

theorem q179_edge62_3 :
    EdgeChecks BoundedLStarData.q179 62 3 ((BoundedLStarData.q179.core 62).edges 3) := by decide +kernel

theorem q179_triangles62 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 62) = true := by decide +kernel

theorem q179_descent62 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 62) = true := by
  change allTriangleDescentsCheck (ofSix (-5) (-2) (1) (24) (-13) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable63 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 63).word) (BoundedLStarData.q179.node 63) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,1,0]) (ofSix (-2) (1) (12) (-3) (-17) (-6))
  rw [q179_prefix63]
  intro u v; rfl

theorem q179_cyclic63 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 63) := by decide +kernel

theorem q179_edge63_0 :
    EdgeChecks BoundedLStarData.q179 63 0 ((BoundedLStarData.q179.core 63).edges 0) := by decide +kernel

theorem q179_edge63_1 :
    EdgeChecks BoundedLStarData.q179 63 1 ((BoundedLStarData.q179.core 63).edges 1) := by decide +kernel

theorem q179_edge63_2 :
    EdgeChecks BoundedLStarData.q179 63 2 ((BoundedLStarData.q179.core 63).edges 2) := by decide +kernel

theorem q179_edge63_3 :
    EdgeChecks BoundedLStarData.q179 63 3 ((BoundedLStarData.q179.core 63).edges 3) := by decide +kernel

theorem q179_triangles63 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 63) = true := by decide +kernel

theorem q179_descent63 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 63) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (1) (12) (-3) (-17) (-6)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
