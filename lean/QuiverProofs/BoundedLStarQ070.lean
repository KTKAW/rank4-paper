import QuiverProofs.BoundedLStarData
import QuiverProofs.LStarCertificate
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem q070_prefix0 : applyWord (BoundedLStarData.q070.node 0) [] = (ofSix (-2) (-2) (-1) (-1) (2) (-2)) := by
  rfl

private theorem q070_prefix1 : applyWord (BoundedLStarData.q070.node 0) [1] = (ofSix (2) (-4) (-1) (1) (-2) (0)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,q070_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix2 : applyWord (BoundedLStarData.q070.node 0) [2] = (ofSix (-2) (2) (-5) (1) (0) (2)) := by
  rw [show ([2] : List (Fin 4)) = [] ++ [2] from rfl,
    applyWord_append,q070_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix3 : applyWord (BoundedLStarData.q070.node 0) [3] = (ofSix (-4) (-2) (1) (3) (-2) (2)) := by
  rw [show ([3] : List (Fin 4)) = [] ++ [3] from rfl,
    applyWord_append,q070_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix4 : applyWord (BoundedLStarData.q070.node 0) [1,0] = (ofSix (-2) (4) (1) (-7) (-4) (0)) := by
  rw [show ([1,0] : List (Fin 4)) = [1] ++ [0] from rfl,
    applyWord_append,q070_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix5 : applyWord (BoundedLStarData.q070.node 0) [1,2] = (ofSix (-2) (4) (-1) (-1) (-2) (0)) := by
  rw [show ([1,2] : List (Fin 4)) = [1] ++ [2] from rfl,
    applyWord_append,q070_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix6 : applyWord (BoundedLStarData.q070.node 0) [2,1] = (ofSix (2) (2) (-5) (-1) (0) (2)) := by
  rw [show ([2,1] : List (Fin 4)) = [2] ++ [1] from rfl,
    applyWord_append,q070_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix7 : applyWord (BoundedLStarData.q070.node 0) [2,3] = (ofSix (-2) (-8) (5) (1) (0) (-2)) := by
  rw [show ([2,3] : List (Fin 4)) = [2] ++ [3] from rfl,
    applyWord_append,q070_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix8 : applyWord (BoundedLStarData.q070.node 0) [3,0] = (ofSix (4) (2) (-1) (3) (2) (4)) := by
  rw [show ([3,0] : List (Fin 4)) = [3] ++ [0] from rfl,
    applyWord_append,q070_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix9 : applyWord (BoundedLStarData.q070.node 0) [1,0,3] = (ofSix (2) (4) (-1) (-7) (4) (0)) := by
  rw [show ([1,0,3] : List (Fin 4)) = [1,0] ++ [3] from rfl,
    applyWord_append,q070_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix10 : applyWord (BoundedLStarData.q070.node 0) [1,2,0] = (ofSix (2) (-4) (1) (7) (-2) (-4)) := by
  rw [show ([1,2,0] : List (Fin 4)) = [1,2] ++ [0] from rfl,
    applyWord_append,q070_prefix5]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix11 : applyWord (BoundedLStarData.q070.node 0) [2,1,3] = (ofSix (2) (-8) (5) (-1) (0) (-2)) := by
  rw [show ([2,1,3] : List (Fin 4)) = [2,1] ++ [3] from rfl,
    applyWord_append,q070_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix12 : applyWord (BoundedLStarData.q070.node 0) [2,3,2] = (ofSix (-10) (8) (-11) (-1) (0) (2)) := by
  rw [show ([2,3,2] : List (Fin 4)) = [2,3] ++ [2] from rfl,
    applyWord_append,q070_prefix7]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix13 : applyWord (BoundedLStarData.q070.node 0) [2,1,3,2] = (ofSix (2) (8) (-11) (1) (-2) (2)) := by
  rw [show ([2,1,3,2] : List (Fin 4)) = [2,1,3] ++ [2] from rfl,
    applyWord_append,q070_prefix11]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_prefix14 : applyWord (BoundedLStarData.q070.node 0) [2,3,2,1] = (ofSix (10) (-2) (-11) (1) (0) (2)) := by
  rw [show ([2,3,2,1] : List (Fin 4)) = [2,3,2] ++ [1] from rfl,
    applyWord_append,q070_prefix12]
  apply entriesEqual_eq
  decide +kernel

private theorem q070_reachable0 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 0).word) (BoundedLStarData.q070.node 0) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) []) (ofSix (-2) (-2) (-1) (-1) (2) (-2))
  rw [q070_prefix0]
  intro u v; rfl

private theorem q070_cyclic0 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 0) := by decide +kernel

private theorem q070_edge0_0 :
    EdgeChecks BoundedLStarData.q070 0 0 ((BoundedLStarData.q070.core 0).edges 0) := by decide +kernel

private theorem q070_edge0_1 :
    EdgeChecks BoundedLStarData.q070 0 1 ((BoundedLStarData.q070.core 0).edges 1) := by decide +kernel

private theorem q070_edge0_2 :
    EdgeChecks BoundedLStarData.q070 0 2 ((BoundedLStarData.q070.core 0).edges 2) := by decide +kernel

private theorem q070_edge0_3 :
    EdgeChecks BoundedLStarData.q070 0 3 ((BoundedLStarData.q070.core 0).edges 3) := by decide +kernel

private theorem q070_triangles0 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 0) = true := by decide +kernel

private theorem q070_descent0 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-2) (-1) (-1) (2) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable1 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 1).word) (BoundedLStarData.q070.node 1) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [1]) (ofSix (2) (-4) (-1) (1) (-2) (0))
  rw [q070_prefix1]
  intro u v; rfl

private theorem q070_cyclic1 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 1) := by decide +kernel

private theorem q070_edge1_0 :
    EdgeChecks BoundedLStarData.q070 1 0 ((BoundedLStarData.q070.core 1).edges 0) := by decide +kernel

private theorem q070_edge1_1 :
    EdgeChecks BoundedLStarData.q070 1 1 ((BoundedLStarData.q070.core 1).edges 1) := by decide +kernel

private theorem q070_edge1_2 :
    EdgeChecks BoundedLStarData.q070 1 2 ((BoundedLStarData.q070.core 1).edges 2) := by decide +kernel

private theorem q070_edge1_3 :
    EdgeChecks BoundedLStarData.q070 1 3 ((BoundedLStarData.q070.core 1).edges 3) := by decide +kernel

private theorem q070_triangles1 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 1) = true := by decide +kernel

private theorem q070_descent1 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-4) (-1) (1) (-2) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable2 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 2).word) (BoundedLStarData.q070.node 2) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [2]) (ofSix (-2) (2) (-5) (1) (0) (2))
  rw [q070_prefix2]
  intro u v; rfl

private theorem q070_cyclic2 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 2) := by decide +kernel

private theorem q070_edge2_0 :
    EdgeChecks BoundedLStarData.q070 2 0 ((BoundedLStarData.q070.core 2).edges 0) := by decide +kernel

private theorem q070_edge2_1 :
    EdgeChecks BoundedLStarData.q070 2 1 ((BoundedLStarData.q070.core 2).edges 1) := by decide +kernel

private theorem q070_edge2_2 :
    EdgeChecks BoundedLStarData.q070 2 2 ((BoundedLStarData.q070.core 2).edges 2) := by decide +kernel

private theorem q070_edge2_3 :
    EdgeChecks BoundedLStarData.q070 2 3 ((BoundedLStarData.q070.core 2).edges 3) := by decide +kernel

private theorem q070_triangles2 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 2) = true := by decide +kernel

private theorem q070_descent2 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (2) (-5) (1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable3 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 3).word) (BoundedLStarData.q070.node 3) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [3]) (ofSix (-4) (-2) (1) (3) (-2) (2))
  rw [q070_prefix3]
  intro u v; rfl

private theorem q070_cyclic3 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 3) := by decide +kernel

private theorem q070_edge3_0 :
    EdgeChecks BoundedLStarData.q070 3 0 ((BoundedLStarData.q070.core 3).edges 0) := by decide +kernel

private theorem q070_edge3_1 :
    EdgeChecks BoundedLStarData.q070 3 1 ((BoundedLStarData.q070.core 3).edges 1) := by decide +kernel

private theorem q070_edge3_2 :
    EdgeChecks BoundedLStarData.q070 3 2 ((BoundedLStarData.q070.core 3).edges 2) := by decide +kernel

private theorem q070_edge3_3 :
    EdgeChecks BoundedLStarData.q070 3 3 ((BoundedLStarData.q070.core 3).edges 3) := by decide +kernel

private theorem q070_triangles3 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 3) = true := by decide +kernel

private theorem q070_descent3 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (-4) (-2) (1) (3) (-2) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable4 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 4).word) (BoundedLStarData.q070.node 4) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [1,0]) (ofSix (-2) (4) (1) (-7) (-4) (0))
  rw [q070_prefix4]
  intro u v; rfl

private theorem q070_cyclic4 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 4) := by decide +kernel

private theorem q070_edge4_0 :
    EdgeChecks BoundedLStarData.q070 4 0 ((BoundedLStarData.q070.core 4).edges 0) := by decide +kernel

private theorem q070_edge4_1 :
    EdgeChecks BoundedLStarData.q070 4 1 ((BoundedLStarData.q070.core 4).edges 1) := by decide +kernel

private theorem q070_edge4_2 :
    EdgeChecks BoundedLStarData.q070 4 2 ((BoundedLStarData.q070.core 4).edges 2) := by decide +kernel

private theorem q070_edge4_3 :
    EdgeChecks BoundedLStarData.q070 4 3 ((BoundedLStarData.q070.core 4).edges 3) := by decide +kernel

private theorem q070_triangles4 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 4) = true := by decide +kernel

private theorem q070_descent4 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (4) (1) (-7) (-4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable5 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 5).word) (BoundedLStarData.q070.node 5) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [1,2]) (ofSix (-2) (4) (-1) (-1) (-2) (0))
  rw [q070_prefix5]
  intro u v; rfl

private theorem q070_cyclic5 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 5) := by decide +kernel

private theorem q070_edge5_0 :
    EdgeChecks BoundedLStarData.q070 5 0 ((BoundedLStarData.q070.core 5).edges 0) := by decide +kernel

private theorem q070_edge5_1 :
    EdgeChecks BoundedLStarData.q070 5 1 ((BoundedLStarData.q070.core 5).edges 1) := by decide +kernel

private theorem q070_edge5_2 :
    EdgeChecks BoundedLStarData.q070 5 2 ((BoundedLStarData.q070.core 5).edges 2) := by decide +kernel

private theorem q070_edge5_3 :
    EdgeChecks BoundedLStarData.q070 5 3 ((BoundedLStarData.q070.core 5).edges 3) := by decide +kernel

private theorem q070_triangles5 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 5) = true := by decide +kernel

private theorem q070_descent5 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (4) (-1) (-1) (-2) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable6 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 6).word) (BoundedLStarData.q070.node 6) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [2,1]) (ofSix (2) (2) (-5) (-1) (0) (2))
  rw [q070_prefix6]
  intro u v; rfl

private theorem q070_cyclic6 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 6) := by decide +kernel

private theorem q070_edge6_0 :
    EdgeChecks BoundedLStarData.q070 6 0 ((BoundedLStarData.q070.core 6).edges 0) := by decide +kernel

private theorem q070_edge6_1 :
    EdgeChecks BoundedLStarData.q070 6 1 ((BoundedLStarData.q070.core 6).edges 1) := by decide +kernel

private theorem q070_edge6_2 :
    EdgeChecks BoundedLStarData.q070 6 2 ((BoundedLStarData.q070.core 6).edges 2) := by decide +kernel

private theorem q070_edge6_3 :
    EdgeChecks BoundedLStarData.q070 6 3 ((BoundedLStarData.q070.core 6).edges 3) := by decide +kernel

private theorem q070_triangles6 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 6) = true := by decide +kernel

private theorem q070_descent6 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (2) (2) (-5) (-1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable7 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 7).word) (BoundedLStarData.q070.node 7) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [2,3]) (ofSix (-2) (-8) (5) (1) (0) (-2))
  rw [q070_prefix7]
  intro u v; rfl

private theorem q070_cyclic7 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 7) := by decide +kernel

private theorem q070_edge7_0 :
    EdgeChecks BoundedLStarData.q070 7 0 ((BoundedLStarData.q070.core 7).edges 0) := by decide +kernel

private theorem q070_edge7_1 :
    EdgeChecks BoundedLStarData.q070 7 1 ((BoundedLStarData.q070.core 7).edges 1) := by decide +kernel

private theorem q070_edge7_2 :
    EdgeChecks BoundedLStarData.q070 7 2 ((BoundedLStarData.q070.core 7).edges 2) := by decide +kernel

private theorem q070_edge7_3 :
    EdgeChecks BoundedLStarData.q070 7 3 ((BoundedLStarData.q070.core 7).edges 3) := by decide +kernel

private theorem q070_triangles7 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 7) = true := by decide +kernel

private theorem q070_descent7 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-8) (5) (1) (0) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable8 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 8).word) (BoundedLStarData.q070.node 8) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [3,0]) (ofSix (4) (2) (-1) (3) (2) (4))
  rw [q070_prefix8]
  intro u v; rfl

private theorem q070_cyclic8 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 8) := by decide +kernel

private theorem q070_edge8_0 :
    EdgeChecks BoundedLStarData.q070 8 0 ((BoundedLStarData.q070.core 8).edges 0) := by decide +kernel

private theorem q070_edge8_1 :
    EdgeChecks BoundedLStarData.q070 8 1 ((BoundedLStarData.q070.core 8).edges 1) := by decide +kernel

private theorem q070_edge8_2 :
    EdgeChecks BoundedLStarData.q070 8 2 ((BoundedLStarData.q070.core 8).edges 2) := by decide +kernel

private theorem q070_edge8_3 :
    EdgeChecks BoundedLStarData.q070 8 3 ((BoundedLStarData.q070.core 8).edges 3) := by decide +kernel

private theorem q070_triangles8 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 8) = true := by decide +kernel

private theorem q070_descent8 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (4) (2) (-1) (3) (2) (4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable9 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 9).word) (BoundedLStarData.q070.node 9) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [1,0,3]) (ofSix (2) (4) (-1) (-7) (4) (0))
  rw [q070_prefix9]
  intro u v; rfl

private theorem q070_cyclic9 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 9) := by decide +kernel

private theorem q070_edge9_0 :
    EdgeChecks BoundedLStarData.q070 9 0 ((BoundedLStarData.q070.core 9).edges 0) := by decide +kernel

private theorem q070_edge9_1 :
    EdgeChecks BoundedLStarData.q070 9 1 ((BoundedLStarData.q070.core 9).edges 1) := by decide +kernel

private theorem q070_edge9_2 :
    EdgeChecks BoundedLStarData.q070 9 2 ((BoundedLStarData.q070.core 9).edges 2) := by decide +kernel

private theorem q070_edge9_3 :
    EdgeChecks BoundedLStarData.q070 9 3 ((BoundedLStarData.q070.core 9).edges 3) := by decide +kernel

private theorem q070_triangles9 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 9) = true := by decide +kernel

private theorem q070_descent9 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (2) (4) (-1) (-7) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable10 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 10).word) (BoundedLStarData.q070.node 10) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [1,2,0]) (ofSix (2) (-4) (1) (7) (-2) (-4))
  rw [q070_prefix10]
  intro u v; rfl

private theorem q070_cyclic10 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 10) := by decide +kernel

private theorem q070_edge10_0 :
    EdgeChecks BoundedLStarData.q070 10 0 ((BoundedLStarData.q070.core 10).edges 0) := by decide +kernel

private theorem q070_edge10_1 :
    EdgeChecks BoundedLStarData.q070 10 1 ((BoundedLStarData.q070.core 10).edges 1) := by decide +kernel

private theorem q070_edge10_2 :
    EdgeChecks BoundedLStarData.q070 10 2 ((BoundedLStarData.q070.core 10).edges 2) := by decide +kernel

private theorem q070_edge10_3 :
    EdgeChecks BoundedLStarData.q070 10 3 ((BoundedLStarData.q070.core 10).edges 3) := by decide +kernel

private theorem q070_triangles10 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 10) = true := by decide +kernel

private theorem q070_descent10 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 10) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-4) (1) (7) (-2) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable11 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 11).word) (BoundedLStarData.q070.node 11) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [2,1,3]) (ofSix (2) (-8) (5) (-1) (0) (-2))
  rw [q070_prefix11]
  intro u v; rfl

private theorem q070_cyclic11 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 11) := by decide +kernel

private theorem q070_edge11_0 :
    EdgeChecks BoundedLStarData.q070 11 0 ((BoundedLStarData.q070.core 11).edges 0) := by decide +kernel

private theorem q070_edge11_1 :
    EdgeChecks BoundedLStarData.q070 11 1 ((BoundedLStarData.q070.core 11).edges 1) := by decide +kernel

private theorem q070_edge11_2 :
    EdgeChecks BoundedLStarData.q070 11 2 ((BoundedLStarData.q070.core 11).edges 2) := by decide +kernel

private theorem q070_edge11_3 :
    EdgeChecks BoundedLStarData.q070 11 3 ((BoundedLStarData.q070.core 11).edges 3) := by decide +kernel

private theorem q070_triangles11 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 11) = true := by decide +kernel

private theorem q070_descent11 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 11) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-8) (5) (-1) (0) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable12 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 12).word) (BoundedLStarData.q070.node 12) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [2,3,2]) (ofSix (-10) (8) (-11) (-1) (0) (2))
  rw [q070_prefix12]
  intro u v; rfl

private theorem q070_cyclic12 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 12) := by decide +kernel

private theorem q070_edge12_0 :
    EdgeChecks BoundedLStarData.q070 12 0 ((BoundedLStarData.q070.core 12).edges 0) := by decide +kernel

private theorem q070_edge12_1 :
    EdgeChecks BoundedLStarData.q070 12 1 ((BoundedLStarData.q070.core 12).edges 1) := by decide +kernel

private theorem q070_edge12_2 :
    EdgeChecks BoundedLStarData.q070 12 2 ((BoundedLStarData.q070.core 12).edges 2) := by decide +kernel

private theorem q070_edge12_3 :
    EdgeChecks BoundedLStarData.q070 12 3 ((BoundedLStarData.q070.core 12).edges 3) := by decide +kernel

private theorem q070_triangles12 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 12) = true := by decide +kernel

private theorem q070_descent12 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 12) = true := by
  change allTriangleDescentsCheck (ofSix (-10) (8) (-11) (-1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable13 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 13).word) (BoundedLStarData.q070.node 13) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [2,1,3,2]) (ofSix (2) (8) (-11) (1) (-2) (2))
  rw [q070_prefix13]
  intro u v; rfl

private theorem q070_cyclic13 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 13) := by decide +kernel

private theorem q070_edge13_0 :
    EdgeChecks BoundedLStarData.q070 13 0 ((BoundedLStarData.q070.core 13).edges 0) := by decide +kernel

private theorem q070_edge13_1 :
    EdgeChecks BoundedLStarData.q070 13 1 ((BoundedLStarData.q070.core 13).edges 1) := by decide +kernel

private theorem q070_edge13_2 :
    EdgeChecks BoundedLStarData.q070 13 2 ((BoundedLStarData.q070.core 13).edges 2) := by decide +kernel

private theorem q070_edge13_3 :
    EdgeChecks BoundedLStarData.q070 13 3 ((BoundedLStarData.q070.core 13).edges 3) := by decide +kernel

private theorem q070_triangles13 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 13) = true := by decide +kernel

private theorem q070_descent13 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 13) = true := by
  change allTriangleDescentsCheck (ofSix (2) (8) (-11) (1) (-2) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q070_reachable14 :
    EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core 14).word) (BoundedLStarData.q070.node 14) := by
  change EntriesEqual (applyWord (BoundedLStarData.q070.node 0) [2,3,2,1]) (ofSix (10) (-2) (-11) (1) (0) (2))
  rw [q070_prefix14]
  intro u v; rfl

private theorem q070_cyclic14 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node 14) := by decide +kernel

private theorem q070_edge14_0 :
    EdgeChecks BoundedLStarData.q070 14 0 ((BoundedLStarData.q070.core 14).edges 0) := by decide +kernel

private theorem q070_edge14_1 :
    EdgeChecks BoundedLStarData.q070 14 1 ((BoundedLStarData.q070.core 14).edges 1) := by decide +kernel

private theorem q070_edge14_2 :
    EdgeChecks BoundedLStarData.q070 14 2 ((BoundedLStarData.q070.core 14).edges 2) := by decide +kernel

private theorem q070_edge14_3 :
    EdgeChecks BoundedLStarData.q070 14 3 ((BoundedLStarData.q070.core 14).edges 3) := by decide +kernel

private theorem q070_triangles14 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node 14) = true := by decide +kernel

private theorem q070_descent14 :
    allTriangleDescentsCheck (BoundedLStarData.q070.node 14) = true := by
  change allTriangleDescentsCheck (ofSix (10) (-2) (-11) (1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q070_reachable : ∀ i, EntriesEqual (applyWord (BoundedLStarData.q070.node 0) (BoundedLStarData.q070.core i).word) (BoundedLStarData.q070.node i) := by
  intro i
  change Fin 15 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q070_reachable0
  · exact q070_reachable1
  · exact q070_reachable2
  · exact q070_reachable3
  · exact q070_reachable4
  · exact q070_reachable5
  · exact q070_reachable6
  · exact q070_reachable7
  · exact q070_reachable8
  · exact q070_reachable9
  · exact q070_reachable10
  · exact q070_reachable11
  · exact q070_reachable12
  · exact q070_reachable13
  · exact q070_reachable14

theorem q070_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q070.node i) := by
  intro i
  change Fin 15 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q070_cyclic0
  · exact q070_cyclic1
  · exact q070_cyclic2
  · exact q070_cyclic3
  · exact q070_cyclic4
  · exact q070_cyclic5
  · exact q070_cyclic6
  · exact q070_cyclic7
  · exact q070_cyclic8
  · exact q070_cyclic9
  · exact q070_cyclic10
  · exact q070_cyclic11
  · exact q070_cyclic12
  · exact q070_cyclic13
  · exact q070_cyclic14

theorem q070_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q070.node i) = true := by
  intro i
  change Fin 15 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q070_triangles0
  · exact q070_triangles1
  · exact q070_triangles2
  · exact q070_triangles3
  · exact q070_triangles4
  · exact q070_triangles5
  · exact q070_triangles6
  · exact q070_triangles7
  · exact q070_triangles8
  · exact q070_triangles9
  · exact q070_triangles10
  · exact q070_triangles11
  · exact q070_triangles12
  · exact q070_triangles13
  · exact q070_triangles14

theorem q070_descents : ∀ i, allTriangleDescentsCheck (BoundedLStarData.q070.node i) = true := by
  intro i
  change Fin 15 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q070_descent0
  · exact q070_descent1
  · exact q070_descent2
  · exact q070_descent3
  · exact q070_descent4
  · exact q070_descent5
  · exact q070_descent6
  · exact q070_descent7
  · exact q070_descent8
  · exact q070_descent9
  · exact q070_descent10
  · exact q070_descent11
  · exact q070_descent12
  · exact q070_descent13
  · exact q070_descent14

theorem q070_edges : ∀ i k, EdgeChecks BoundedLStarData.q070 i k ((BoundedLStarData.q070.core i).edges k) := by
  intro i k
  change Fin 15 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge0_0
    · exact q070_edge0_1
    · exact q070_edge0_2
    · exact q070_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge1_0
    · exact q070_edge1_1
    · exact q070_edge1_2
    · exact q070_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge2_0
    · exact q070_edge2_1
    · exact q070_edge2_2
    · exact q070_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge3_0
    · exact q070_edge3_1
    · exact q070_edge3_2
    · exact q070_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge4_0
    · exact q070_edge4_1
    · exact q070_edge4_2
    · exact q070_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge5_0
    · exact q070_edge5_1
    · exact q070_edge5_2
    · exact q070_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge6_0
    · exact q070_edge6_1
    · exact q070_edge6_2
    · exact q070_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge7_0
    · exact q070_edge7_1
    · exact q070_edge7_2
    · exact q070_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge8_0
    · exact q070_edge8_1
    · exact q070_edge8_2
    · exact q070_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge9_0
    · exact q070_edge9_1
    · exact q070_edge9_2
    · exact q070_edge9_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge10_0
    · exact q070_edge10_1
    · exact q070_edge10_2
    · exact q070_edge10_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge11_0
    · exact q070_edge11_1
    · exact q070_edge11_2
    · exact q070_edge11_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge12_0
    · exact q070_edge12_1
    · exact q070_edge12_2
    · exact q070_edge12_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge13_0
    · exact q070_edge13_1
    · exact q070_edge13_2
    · exact q070_edge13_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q070_edge14_0
    · exact q070_edge14_1
    · exact q070_edge14_2
    · exact q070_edge14_3

theorem q070_checks : Checks BoundedLStarData.q070 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := q070_reachable
  cyclic := q070_cyclic
  strips := by
    intro s
    change Fin 0 at s
    exact Fin.elim0 s
  edges := q070_edges
  triangles := (decide_eq_true q070_triangles).symm
  descents := fun _ => q070_descents

end QuiverProofs.BoundedLStarChecks
