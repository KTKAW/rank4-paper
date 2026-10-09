import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_reachable76 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 76).word) (BoundedLStarData.q179.node 76) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,2,3]) (ofSix (-53) (-1) (3) (-11) (-13) (-1))
  rw [q179_prefix76]
  intro u v; rfl

theorem q179_cyclic76 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 76) := by decide +kernel

theorem q179_edge76_0 :
    EdgeChecks BoundedLStarData.q179 76 0 ((BoundedLStarData.q179.core 76).edges 0) := by decide +kernel

theorem q179_edge76_1 :
    EdgeChecks BoundedLStarData.q179 76 1 ((BoundedLStarData.q179.core 76).edges 1) := by decide +kernel

theorem q179_edge76_2 :
    EdgeChecks BoundedLStarData.q179 76 2 ((BoundedLStarData.q179.core 76).edges 2) := by decide +kernel

theorem q179_edge76_3 :
    EdgeChecks BoundedLStarData.q179 76 3 ((BoundedLStarData.q179.core 76).edges 3) := by decide +kernel

theorem q179_triangles76 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 76) = true := by decide +kernel

theorem q179_descent76 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 76) = true := by
  change allTriangleDescentsCheck (ofSix (-53) (-1) (3) (-11) (-13) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable77 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 77).word) (BoundedLStarData.q179.node 77) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,3,2]) (ofSix (-53) (2) (1) (-24) (11) (-1))
  rw [q179_prefix77]
  intro u v; rfl

theorem q179_cyclic77 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 77) := by decide +kernel

theorem q179_edge77_0 :
    EdgeChecks BoundedLStarData.q179 77 0 ((BoundedLStarData.q179.core 77).edges 0) := by decide +kernel

theorem q179_edge77_1 :
    EdgeChecks BoundedLStarData.q179 77 1 ((BoundedLStarData.q179.core 77).edges 1) := by decide +kernel

theorem q179_edge77_2 :
    EdgeChecks BoundedLStarData.q179 77 2 ((BoundedLStarData.q179.core 77).edges 2) := by decide +kernel

theorem q179_edge77_3 :
    EdgeChecks BoundedLStarData.q179 77 3 ((BoundedLStarData.q179.core 77).edges 3) := by decide +kernel

theorem q179_triangles77 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 77) = true := by decide +kernel

theorem q179_descent77 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 77) = true := by
  change allTriangleDescentsCheck (ofSix (-53) (2) (1) (-24) (11) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable78 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 78).word) (BoundedLStarData.q179.node 78) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,1,0,2]) (ofSix (1) (-1) (12) (3) (-35) (6))
  rw [q179_prefix78]
  intro u v; rfl

theorem q179_cyclic78 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 78) := by decide +kernel

theorem q179_edge78_0 :
    EdgeChecks BoundedLStarData.q179 78 0 ((BoundedLStarData.q179.core 78).edges 0) := by decide +kernel

theorem q179_edge78_1 :
    EdgeChecks BoundedLStarData.q179 78 1 ((BoundedLStarData.q179.core 78).edges 1) := by decide +kernel

theorem q179_edge78_2 :
    EdgeChecks BoundedLStarData.q179 78 2 ((BoundedLStarData.q179.core 78).edges 2) := by decide +kernel

theorem q179_edge78_3 :
    EdgeChecks BoundedLStarData.q179 78 3 ((BoundedLStarData.q179.core 78).edges 3) := by decide +kernel

theorem q179_triangles78 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 78) = true := by decide +kernel

theorem q179_descent78 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 78) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-1) (12) (3) (-35) (6)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q179_reachable79 :
    EntriesEqual (applyWord (BoundedLStarData.q179.node 0) (BoundedLStarData.q179.core 79).word) (BoundedLStarData.q179.node 79) := by
  change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,2,3]) (ofSix (2741) (1) (-9) (299) (43) (1))
  rw [q179_prefix80]
  intro u v; rfl

theorem q179_cyclic79 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q179.node 79) := by decide +kernel

theorem q179_edge79_0 :
    EdgeChecks BoundedLStarData.q179 79 0 ((BoundedLStarData.q179.core 79).edges 0) := by decide +kernel

theorem q179_edge79_1 :
    EdgeChecks BoundedLStarData.q179 79 1 ((BoundedLStarData.q179.core 79).edges 1) := by decide +kernel

theorem q179_edge79_2 :
    EdgeChecks BoundedLStarData.q179 79 2 ((BoundedLStarData.q179.core 79).edges 2) := by decide +kernel

theorem q179_edge79_3 :
    EdgeChecks BoundedLStarData.q179 79 3 ((BoundedLStarData.q179.core 79).edges 3) := by decide +kernel

theorem q179_triangles79 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q179.node 79) = true := by decide +kernel

theorem q179_descent79 :
    allTriangleDescentsCheck (BoundedLStarData.q179.node 79) = true := by
  change allTriangleDescentsCheck (ofSix (2741) (1) (-9) (299) (43) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

end QuiverProofs.BoundedLStarChecks
