import QuiverProofs.BoundedLStarData
import QuiverProofs.LStarCertificate
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem q455_prefix0 : applyWord (BoundedLStarData.q455.node 0) [] = (ofSix (-2) (-1) (1) (0) (-2) (1)) := by
  rfl

private theorem q455_prefix1 : applyWord (BoundedLStarData.q455.node 0) [0] = (ofSix (2) (1) (-1) (0) (0) (2)) := by
  rw [show ([0] : List (Fin 4)) = [] ++ [0] from rfl,
    applyWord_append,q455_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix2 : applyWord (BoundedLStarData.q455.node 0) [1] = (ofSix (2) (-1) (-3) (0) (2) (1)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,q455_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix3 : applyWord (BoundedLStarData.q455.node 0) [1,0] = (ofSix (-2) (1) (3) (-2) (-4) (1)) := by
  rw [show ([1,0] : List (Fin 4)) = [1] ++ [0] from rfl,
    applyWord_append,q455_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix4 : applyWord (BoundedLStarData.q455.node 0) [1,3] = (ofSix (-4) (-4) (3) (0) (-2) (-1)) := by
  rw [show ([1,3] : List (Fin 4)) = [1] ++ [3] from rfl,
    applyWord_append,q455_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix5 : applyWord (BoundedLStarData.q455.node 0) [1,0,2] = (ofSix (0) (-1) (4) (2) (-4) (-1)) := by
  rw [show ([1,0,2] : List (Fin 4)) = [1,0] ++ [2] from rfl,
    applyWord_append,q455_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix6 : applyWord (BoundedLStarData.q455.node 0) [1,0,3] = (ofSix (10) (1) (-3) (-6) (4) (-1)) := by
  rw [show ([1,0,3] : List (Fin 4)) = [1,0] ++ [3] from rfl,
    applyWord_append,q455_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix7 : applyWord (BoundedLStarData.q455.node 0) [1,0,2,3] = (ofSix (16) (3) (-4) (2) (4) (1)) := by
  rw [show ([1,0,2,3] : List (Fin 4)) = [1,0,2] ++ [3] from rfl,
    applyWord_append,q455_prefix5]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix8 : applyWord (BoundedLStarData.q455.node 0) [1,0,3,0] = (ofSix (-10) (-1) (3) (-6) (-26) (-4)) := by
  rw [show ([1,0,3,0] : List (Fin 4)) = [1,0,3] ++ [0] from rfl,
    applyWord_append,q455_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix9 : applyWord (BoundedLStarData.q455.node 0) [1,0,3,2] = (ofSix (16) (-1) (-3) (6) (-2) (1)) := by
  rw [show ([1,0,3,2] : List (Fin 4)) = [1,0,3] ++ [2] from rfl,
    applyWord_append,q455_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix10 : applyWord (BoundedLStarData.q455.node 0) [1,0,3,0,2] = (ofSix (-10) (1) (-1) (6) (-50) (4)) := by
  rw [show ([1,0,3,0,2] : List (Fin 4)) = [1,0,3,0] ++ [2] from rfl,
    applyWord_append,q455_prefix8]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix11 : applyWord (BoundedLStarData.q455.node 0) [1,0,3,2,0] = (ofSix (-16) (1) (3) (-10) (-50) (1)) := by
  rw [show ([1,0,3,2,0] : List (Fin 4)) = [1,0,3,2] ++ [0] from rfl,
    applyWord_append,q455_prefix9]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_prefix12 : applyWord (BoundedLStarData.q455.node 0) [1,0,3,0,2,3] = (ofSix (-10) (-3) (1) (-194) (50) (-4)) := by
  rw [show ([1,0,3,0,2,3] : List (Fin 4)) = [1,0,3,0,2] ++ [3] from rfl,
    applyWord_append,q455_prefix10]
  apply entriesEqual_eq
  decide +kernel

private theorem q455_reachable0 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 0).word) (BoundedLStarData.q455.node 0) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) []) (ofSix (-2) (-1) (1) (0) (-2) (1))
  rw [q455_prefix0]
  intro u v; rfl

private theorem q455_cyclic0 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 0) := by decide +kernel

private theorem q455_edge0_0 :
    EdgeChecks BoundedLStarData.q455 0 0 ((BoundedLStarData.q455.core 0).edges 0) := by decide +kernel

private theorem q455_edge0_1 :
    EdgeChecks BoundedLStarData.q455 0 1 ((BoundedLStarData.q455.core 0).edges 1) := by decide +kernel

private theorem q455_edge0_2 :
    EdgeChecks BoundedLStarData.q455 0 2 ((BoundedLStarData.q455.core 0).edges 2) := by decide +kernel

private theorem q455_edge0_3 :
    EdgeChecks BoundedLStarData.q455 0 3 ((BoundedLStarData.q455.core 0).edges 3) := by decide +kernel

private theorem q455_triangles0 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 0) = true := by decide +kernel

private theorem q455_descent0 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-1) (1) (0) (-2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable1 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 1).word) (BoundedLStarData.q455.node 1) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [0]) (ofSix (2) (1) (-1) (0) (0) (2))
  rw [q455_prefix1]
  intro u v; rfl

private theorem q455_cyclic1 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 1) := by decide +kernel

private theorem q455_edge1_0 :
    EdgeChecks BoundedLStarData.q455 1 0 ((BoundedLStarData.q455.core 1).edges 0) := by decide +kernel

private theorem q455_edge1_1 :
    EdgeChecks BoundedLStarData.q455 1 1 ((BoundedLStarData.q455.core 1).edges 1) := by decide +kernel

private theorem q455_edge1_2 :
    EdgeChecks BoundedLStarData.q455 1 2 ((BoundedLStarData.q455.core 1).edges 2) := by decide +kernel

private theorem q455_edge1_3 :
    EdgeChecks BoundedLStarData.q455 1 3 ((BoundedLStarData.q455.core 1).edges 3) := by decide +kernel

private theorem q455_triangles1 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 1) = true := by decide +kernel

private theorem q455_descent1 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (1) (-1) (0) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable2 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 2).word) (BoundedLStarData.q455.node 2) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1]) (ofSix (2) (-1) (-3) (0) (2) (1))
  rw [q455_prefix2]
  intro u v; rfl

private theorem q455_cyclic2 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 2) := by decide +kernel

private theorem q455_edge2_0 :
    EdgeChecks BoundedLStarData.q455 2 0 ((BoundedLStarData.q455.core 2).edges 0) := by decide +kernel

private theorem q455_edge2_1 :
    EdgeChecks BoundedLStarData.q455 2 1 ((BoundedLStarData.q455.core 2).edges 1) := by decide +kernel

private theorem q455_edge2_2 :
    EdgeChecks BoundedLStarData.q455 2 2 ((BoundedLStarData.q455.core 2).edges 2) := by decide +kernel

private theorem q455_edge2_3 :
    EdgeChecks BoundedLStarData.q455 2 3 ((BoundedLStarData.q455.core 2).edges 3) := by decide +kernel

private theorem q455_triangles2 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 2) = true := by decide +kernel

private theorem q455_descent2 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (-3) (0) (2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable3 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 3).word) (BoundedLStarData.q455.node 3) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0]) (ofSix (-2) (1) (3) (-2) (-4) (1))
  rw [q455_prefix3]
  intro u v; rfl

private theorem q455_cyclic3 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 3) := by decide +kernel

private theorem q455_edge3_0 :
    EdgeChecks BoundedLStarData.q455 3 0 ((BoundedLStarData.q455.core 3).edges 0) := by decide +kernel

private theorem q455_edge3_1 :
    EdgeChecks BoundedLStarData.q455 3 1 ((BoundedLStarData.q455.core 3).edges 1) := by decide +kernel

private theorem q455_edge3_2 :
    EdgeChecks BoundedLStarData.q455 3 2 ((BoundedLStarData.q455.core 3).edges 2) := by decide +kernel

private theorem q455_edge3_3 :
    EdgeChecks BoundedLStarData.q455 3 3 ((BoundedLStarData.q455.core 3).edges 3) := by decide +kernel

private theorem q455_triangles3 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 3) = true := by decide +kernel

private theorem q455_descent3 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (1) (3) (-2) (-4) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable4 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 4).word) (BoundedLStarData.q455.node 4) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,3]) (ofSix (-4) (-4) (3) (0) (-2) (-1))
  rw [q455_prefix4]
  intro u v; rfl

private theorem q455_cyclic4 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 4) := by decide +kernel

private theorem q455_edge4_0 :
    EdgeChecks BoundedLStarData.q455 4 0 ((BoundedLStarData.q455.core 4).edges 0) := by decide +kernel

private theorem q455_edge4_1 :
    EdgeChecks BoundedLStarData.q455 4 1 ((BoundedLStarData.q455.core 4).edges 1) := by decide +kernel

private theorem q455_edge4_2 :
    EdgeChecks BoundedLStarData.q455 4 2 ((BoundedLStarData.q455.core 4).edges 2) := by decide +kernel

private theorem q455_edge4_3 :
    EdgeChecks BoundedLStarData.q455 4 3 ((BoundedLStarData.q455.core 4).edges 3) := by decide +kernel

private theorem q455_triangles4 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 4) = true := by decide +kernel

private theorem q455_descent4 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (-4) (-4) (3) (0) (-2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable5 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 5).word) (BoundedLStarData.q455.node 5) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,2]) (ofSix (0) (-1) (4) (2) (-4) (-1))
  rw [q455_prefix5]
  intro u v; rfl

private theorem q455_cyclic5 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 5) := by decide +kernel

private theorem q455_edge5_0 :
    EdgeChecks BoundedLStarData.q455 5 0 ((BoundedLStarData.q455.core 5).edges 0) := by decide +kernel

private theorem q455_edge5_1 :
    EdgeChecks BoundedLStarData.q455 5 1 ((BoundedLStarData.q455.core 5).edges 1) := by decide +kernel

private theorem q455_edge5_2 :
    EdgeChecks BoundedLStarData.q455 5 2 ((BoundedLStarData.q455.core 5).edges 2) := by decide +kernel

private theorem q455_edge5_3 :
    EdgeChecks BoundedLStarData.q455 5 3 ((BoundedLStarData.q455.core 5).edges 3) := by decide +kernel

private theorem q455_triangles5 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 5) = true := by decide +kernel

private theorem q455_descent5 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-1) (4) (2) (-4) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable6 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 6).word) (BoundedLStarData.q455.node 6) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,3]) (ofSix (10) (1) (-3) (-6) (4) (-1))
  rw [q455_prefix6]
  intro u v; rfl

private theorem q455_cyclic6 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 6) := by decide +kernel

private theorem q455_edge6_0 :
    EdgeChecks BoundedLStarData.q455 6 0 ((BoundedLStarData.q455.core 6).edges 0) := by decide +kernel

private theorem q455_edge6_1 :
    EdgeChecks BoundedLStarData.q455 6 1 ((BoundedLStarData.q455.core 6).edges 1) := by decide +kernel

private theorem q455_edge6_2 :
    EdgeChecks BoundedLStarData.q455 6 2 ((BoundedLStarData.q455.core 6).edges 2) := by decide +kernel

private theorem q455_edge6_3 :
    EdgeChecks BoundedLStarData.q455 6 3 ((BoundedLStarData.q455.core 6).edges 3) := by decide +kernel

private theorem q455_triangles6 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 6) = true := by decide +kernel

private theorem q455_descent6 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (10) (1) (-3) (-6) (4) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable7 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 7).word) (BoundedLStarData.q455.node 7) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,2,3]) (ofSix (16) (3) (-4) (2) (4) (1))
  rw [q455_prefix7]
  intro u v; rfl

private theorem q455_cyclic7 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 7) := by decide +kernel

private theorem q455_edge7_0 :
    EdgeChecks BoundedLStarData.q455 7 0 ((BoundedLStarData.q455.core 7).edges 0) := by decide +kernel

private theorem q455_edge7_1 :
    EdgeChecks BoundedLStarData.q455 7 1 ((BoundedLStarData.q455.core 7).edges 1) := by decide +kernel

private theorem q455_edge7_2 :
    EdgeChecks BoundedLStarData.q455 7 2 ((BoundedLStarData.q455.core 7).edges 2) := by decide +kernel

private theorem q455_edge7_3 :
    EdgeChecks BoundedLStarData.q455 7 3 ((BoundedLStarData.q455.core 7).edges 3) := by decide +kernel

private theorem q455_triangles7 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 7) = true := by decide +kernel

private theorem q455_descent7 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (16) (3) (-4) (2) (4) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable8 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 8).word) (BoundedLStarData.q455.node 8) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,3,0]) (ofSix (-10) (-1) (3) (-6) (-26) (-4))
  rw [q455_prefix8]
  intro u v; rfl

private theorem q455_cyclic8 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 8) := by decide +kernel

private theorem q455_edge8_0 :
    EdgeChecks BoundedLStarData.q455 8 0 ((BoundedLStarData.q455.core 8).edges 0) := by decide +kernel

private theorem q455_edge8_1 :
    EdgeChecks BoundedLStarData.q455 8 1 ((BoundedLStarData.q455.core 8).edges 1) := by decide +kernel

private theorem q455_edge8_2 :
    EdgeChecks BoundedLStarData.q455 8 2 ((BoundedLStarData.q455.core 8).edges 2) := by decide +kernel

private theorem q455_edge8_3 :
    EdgeChecks BoundedLStarData.q455 8 3 ((BoundedLStarData.q455.core 8).edges 3) := by decide +kernel

private theorem q455_triangles8 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 8) = true := by decide +kernel

private theorem q455_descent8 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (-10) (-1) (3) (-6) (-26) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable9 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 9).word) (BoundedLStarData.q455.node 9) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,3,2]) (ofSix (16) (-1) (-3) (6) (-2) (1))
  rw [q455_prefix9]
  intro u v; rfl

private theorem q455_cyclic9 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 9) := by decide +kernel

private theorem q455_edge9_0 :
    EdgeChecks BoundedLStarData.q455 9 0 ((BoundedLStarData.q455.core 9).edges 0) := by decide +kernel

private theorem q455_edge9_1 :
    EdgeChecks BoundedLStarData.q455 9 1 ((BoundedLStarData.q455.core 9).edges 1) := by decide +kernel

private theorem q455_edge9_2 :
    EdgeChecks BoundedLStarData.q455 9 2 ((BoundedLStarData.q455.core 9).edges 2) := by decide +kernel

private theorem q455_edge9_3 :
    EdgeChecks BoundedLStarData.q455 9 3 ((BoundedLStarData.q455.core 9).edges 3) := by decide +kernel

private theorem q455_triangles9 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 9) = true := by decide +kernel

private theorem q455_descent9 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (16) (-1) (-3) (6) (-2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable10 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 10).word) (BoundedLStarData.q455.node 10) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,3,0,2]) (ofSix (-10) (1) (-1) (6) (-50) (4))
  rw [q455_prefix10]
  intro u v; rfl

private theorem q455_cyclic10 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 10) := by decide +kernel

private theorem q455_edge10_0 :
    EdgeChecks BoundedLStarData.q455 10 0 ((BoundedLStarData.q455.core 10).edges 0) := by decide +kernel

private theorem q455_edge10_1 :
    EdgeChecks BoundedLStarData.q455 10 1 ((BoundedLStarData.q455.core 10).edges 1) := by decide +kernel

private theorem q455_edge10_2 :
    EdgeChecks BoundedLStarData.q455 10 2 ((BoundedLStarData.q455.core 10).edges 2) := by decide +kernel

private theorem q455_edge10_3 :
    EdgeChecks BoundedLStarData.q455 10 3 ((BoundedLStarData.q455.core 10).edges 3) := by decide +kernel

private theorem q455_triangles10 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 10) = true := by decide +kernel

private theorem q455_descent10 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 10) = true := by
  change allTriangleDescentsCheck (ofSix (-10) (1) (-1) (6) (-50) (4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable11 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 11).word) (BoundedLStarData.q455.node 11) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,3,2,0]) (ofSix (-16) (1) (3) (-10) (-50) (1))
  rw [q455_prefix11]
  intro u v; rfl

private theorem q455_cyclic11 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 11) := by decide +kernel

private theorem q455_edge11_0 :
    EdgeChecks BoundedLStarData.q455 11 0 ((BoundedLStarData.q455.core 11).edges 0) := by decide +kernel

private theorem q455_edge11_1 :
    EdgeChecks BoundedLStarData.q455 11 1 ((BoundedLStarData.q455.core 11).edges 1) := by decide +kernel

private theorem q455_edge11_2 :
    EdgeChecks BoundedLStarData.q455 11 2 ((BoundedLStarData.q455.core 11).edges 2) := by decide +kernel

private theorem q455_edge11_3 :
    EdgeChecks BoundedLStarData.q455 11 3 ((BoundedLStarData.q455.core 11).edges 3) := by decide +kernel

private theorem q455_triangles11 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 11) = true := by decide +kernel

private theorem q455_descent11 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 11) = true := by
  change allTriangleDescentsCheck (ofSix (-16) (1) (3) (-10) (-50) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_reachable12 :
    EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core 12).word) (BoundedLStarData.q455.node 12) := by
  change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,3,0,2,3]) (ofSix (-10) (-3) (1) (-194) (50) (-4))
  rw [q455_prefix12]
  intro u v; rfl

private theorem q455_cyclic12 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node 12) := by decide +kernel

private theorem q455_edge12_0 :
    EdgeChecks BoundedLStarData.q455 12 0 ((BoundedLStarData.q455.core 12).edges 0) := by decide +kernel

private theorem q455_edge12_1 :
    EdgeChecks BoundedLStarData.q455 12 1 ((BoundedLStarData.q455.core 12).edges 1) := by decide +kernel

private theorem q455_edge12_2 :
    EdgeChecks BoundedLStarData.q455 12 2 ((BoundedLStarData.q455.core 12).edges 2) := by decide +kernel

private theorem q455_edge12_3 :
    EdgeChecks BoundedLStarData.q455 12 3 ((BoundedLStarData.q455.core 12).edges 3) := by decide +kernel

private theorem q455_triangles12 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node 12) = true := by decide +kernel

private theorem q455_descent12 :
    allTriangleDescentsCheck (BoundedLStarData.q455.node 12) = true := by
  change allTriangleDescentsCheck (ofSix (-10) (-3) (1) (-194) (50) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q455_strip0 : StripChecks BoundedLStarData.q455 (BoundedLStarData.q455.strips (0 : Fin 1)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (BoundedLStarData.q455.node 0) [1,0,3,2,0]) (BoundedLStarData.q455.node 11)
    rw [q455_prefix11]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

theorem q455_reachable : ∀ i, EntriesEqual (applyWord (BoundedLStarData.q455.node 0) (BoundedLStarData.q455.core i).word) (BoundedLStarData.q455.node i) := by
  intro i
  change Fin 13 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q455_reachable0
  · exact q455_reachable1
  · exact q455_reachable2
  · exact q455_reachable3
  · exact q455_reachable4
  · exact q455_reachable5
  · exact q455_reachable6
  · exact q455_reachable7
  · exact q455_reachable8
  · exact q455_reachable9
  · exact q455_reachable10
  · exact q455_reachable11
  · exact q455_reachable12

theorem q455_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q455.node i) := by
  intro i
  change Fin 13 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q455_cyclic0
  · exact q455_cyclic1
  · exact q455_cyclic2
  · exact q455_cyclic3
  · exact q455_cyclic4
  · exact q455_cyclic5
  · exact q455_cyclic6
  · exact q455_cyclic7
  · exact q455_cyclic8
  · exact q455_cyclic9
  · exact q455_cyclic10
  · exact q455_cyclic11
  · exact q455_cyclic12

theorem q455_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q455.node i) = true := by
  intro i
  change Fin 13 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q455_triangles0
  · exact q455_triangles1
  · exact q455_triangles2
  · exact q455_triangles3
  · exact q455_triangles4
  · exact q455_triangles5
  · exact q455_triangles6
  · exact q455_triangles7
  · exact q455_triangles8
  · exact q455_triangles9
  · exact q455_triangles10
  · exact q455_triangles11
  · exact q455_triangles12

theorem q455_descents : ∀ i, allTriangleDescentsCheck (BoundedLStarData.q455.node i) = true := by
  intro i
  change Fin 13 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q455_descent0
  · exact q455_descent1
  · exact q455_descent2
  · exact q455_descent3
  · exact q455_descent4
  · exact q455_descent5
  · exact q455_descent6
  · exact q455_descent7
  · exact q455_descent8
  · exact q455_descent9
  · exact q455_descent10
  · exact q455_descent11
  · exact q455_descent12

theorem q455_edges : ∀ i k, EdgeChecks BoundedLStarData.q455 i k ((BoundedLStarData.q455.core i).edges k) := by
  intro i k
  change Fin 13 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge0_0
    · exact q455_edge0_1
    · exact q455_edge0_2
    · exact q455_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge1_0
    · exact q455_edge1_1
    · exact q455_edge1_2
    · exact q455_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge2_0
    · exact q455_edge2_1
    · exact q455_edge2_2
    · exact q455_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge3_0
    · exact q455_edge3_1
    · exact q455_edge3_2
    · exact q455_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge4_0
    · exact q455_edge4_1
    · exact q455_edge4_2
    · exact q455_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge5_0
    · exact q455_edge5_1
    · exact q455_edge5_2
    · exact q455_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge6_0
    · exact q455_edge6_1
    · exact q455_edge6_2
    · exact q455_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge7_0
    · exact q455_edge7_1
    · exact q455_edge7_2
    · exact q455_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge8_0
    · exact q455_edge8_1
    · exact q455_edge8_2
    · exact q455_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge9_0
    · exact q455_edge9_1
    · exact q455_edge9_2
    · exact q455_edge9_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge10_0
    · exact q455_edge10_1
    · exact q455_edge10_2
    · exact q455_edge10_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge11_0
    · exact q455_edge11_1
    · exact q455_edge11_2
    · exact q455_edge11_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q455_edge12_0
    · exact q455_edge12_1
    · exact q455_edge12_2
    · exact q455_edge12_3

theorem q455_checks : Checks BoundedLStarData.q455 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := q455_reachable
  cyclic := q455_cyclic
  strips := by
    intro s
    change Fin 1 at s
    have h : s=0 := by omega
    subst s
    exact q455_strip0
  edges := q455_edges
  triangles := (decide_eq_true q455_triangles).symm
  descents := fun _ => q455_descents

end QuiverProofs.BoundedLStarChecks
