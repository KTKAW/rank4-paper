import QuiverProofs.BoundedLStarData
import QuiverProofs.LStarCertificate
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem q013_prefix0 : applyWord (BoundedLStarData.q013.node 0) [] = (ofSix (-2) (-2) (-2) (-2) (1) (-2)) := by
  rfl

private theorem q013_prefix1 : applyWord (BoundedLStarData.q013.node 0) [1] = (ofSix (2) (-6) (-2) (2) (-1) (0)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,q013_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix2 : applyWord (BoundedLStarData.q013.node 0) [3] = (ofSix (-4) (-2) (2) (0) (-1) (2)) := by
  rw [show ([3] : List (Fin 4)) = [] ++ [3] from rfl,
    applyWord_append,q013_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix3 : applyWord (BoundedLStarData.q013.node 0) [1,2] = (ofSix (-10) (6) (-2) (-2) (-1) (0)) := by
  rw [show ([1,2] : List (Fin 4)) = [1] ++ [2] from rfl,
    applyWord_append,q013_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix4 : applyWord (BoundedLStarData.q013.node 0) [1,3] = (ofSix (2) (-6) (2) (2) (1) (0)) := by
  rw [show ([1,3] : List (Fin 4)) = [1] ++ [3] from rfl,
    applyWord_append,q013_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix5 : applyWord (BoundedLStarData.q013.node 0) [3,1] = (ofSix (4) (-2) (-2) (0) (1) (2)) := by
  rw [show ([3,1] : List (Fin 4)) = [3] ++ [1] from rfl,
    applyWord_append,q013_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix6 : applyWord (BoundedLStarData.q013.node 0) [1,2,1] = (ofSix (10) (-14) (-12) (2) (1) (0)) := by
  rw [show ([1,2,1] : List (Fin 4)) = [1,2] ++ [1] from rfl,
    applyWord_append,q013_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix7 : applyWord (BoundedLStarData.q013.node 0) [1,2,3] = (ofSix (-10) (6) (2) (-2) (1) (0)) := by
  rw [show ([1,2,3] : List (Fin 4)) = [1,2] ++ [3] from rfl,
    applyWord_append,q013_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix8 : applyWord (BoundedLStarData.q013.node 0) [1,2,1,3] = (ofSix (-2) (-14) (12) (2) (-1) (0)) := by
  rw [show ([1,2,1,3] : List (Fin 4)) = [1,2,1] ++ [3] from rfl,
    applyWord_append,q013_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_prefix9 : applyWord (BoundedLStarData.q013.node 0) [1,2,3,1] = (ofSix (10) (-14) (2) (2) (-1) (2)) := by
  rw [show ([1,2,3,1] : List (Fin 4)) = [1,2,3] ++ [1] from rfl,
    applyWord_append,q013_prefix7]
  apply entriesEqual_eq
  decide +kernel

private theorem q013_reachable0 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 0).word) (BoundedLStarData.q013.node 0) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) []) (ofSix (-2) (-2) (-2) (-2) (1) (-2))
  rw [q013_prefix0]
  intro u v; rfl

private theorem q013_cyclic0 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 0) := by decide +kernel

private theorem q013_edge0_0 :
    EdgeChecks BoundedLStarData.q013 0 0 ((BoundedLStarData.q013.core 0).edges 0) := by decide +kernel

private theorem q013_edge0_1 :
    EdgeChecks BoundedLStarData.q013 0 1 ((BoundedLStarData.q013.core 0).edges 1) := by decide +kernel

private theorem q013_edge0_2 :
    EdgeChecks BoundedLStarData.q013 0 2 ((BoundedLStarData.q013.core 0).edges 2) := by decide +kernel

private theorem q013_edge0_3 :
    EdgeChecks BoundedLStarData.q013 0 3 ((BoundedLStarData.q013.core 0).edges 3) := by decide +kernel

private theorem q013_triangles0 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 0) = true := by decide +kernel

private theorem q013_descent0 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-2) (-2) (-2) (1) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable1 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 1).word) (BoundedLStarData.q013.node 1) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [1]) (ofSix (2) (-6) (-2) (2) (-1) (0))
  rw [q013_prefix1]
  intro u v; rfl

private theorem q013_cyclic1 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 1) := by decide +kernel

private theorem q013_edge1_0 :
    EdgeChecks BoundedLStarData.q013 1 0 ((BoundedLStarData.q013.core 1).edges 0) := by decide +kernel

private theorem q013_edge1_1 :
    EdgeChecks BoundedLStarData.q013 1 1 ((BoundedLStarData.q013.core 1).edges 1) := by decide +kernel

private theorem q013_edge1_2 :
    EdgeChecks BoundedLStarData.q013 1 2 ((BoundedLStarData.q013.core 1).edges 2) := by decide +kernel

private theorem q013_edge1_3 :
    EdgeChecks BoundedLStarData.q013 1 3 ((BoundedLStarData.q013.core 1).edges 3) := by decide +kernel

private theorem q013_triangles1 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 1) = true := by decide +kernel

private theorem q013_descent1 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-6) (-2) (2) (-1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable2 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 2).word) (BoundedLStarData.q013.node 2) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [3]) (ofSix (-4) (-2) (2) (0) (-1) (2))
  rw [q013_prefix2]
  intro u v; rfl

private theorem q013_cyclic2 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 2) := by decide +kernel

private theorem q013_edge2_0 :
    EdgeChecks BoundedLStarData.q013 2 0 ((BoundedLStarData.q013.core 2).edges 0) := by decide +kernel

private theorem q013_edge2_1 :
    EdgeChecks BoundedLStarData.q013 2 1 ((BoundedLStarData.q013.core 2).edges 1) := by decide +kernel

private theorem q013_edge2_2 :
    EdgeChecks BoundedLStarData.q013 2 2 ((BoundedLStarData.q013.core 2).edges 2) := by decide +kernel

private theorem q013_edge2_3 :
    EdgeChecks BoundedLStarData.q013 2 3 ((BoundedLStarData.q013.core 2).edges 3) := by decide +kernel

private theorem q013_triangles2 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 2) = true := by decide +kernel

private theorem q013_descent2 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (-4) (-2) (2) (0) (-1) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable3 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 3).word) (BoundedLStarData.q013.node 3) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [1,2]) (ofSix (-10) (6) (-2) (-2) (-1) (0))
  rw [q013_prefix3]
  intro u v; rfl

private theorem q013_cyclic3 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 3) := by decide +kernel

private theorem q013_edge3_0 :
    EdgeChecks BoundedLStarData.q013 3 0 ((BoundedLStarData.q013.core 3).edges 0) := by decide +kernel

private theorem q013_edge3_1 :
    EdgeChecks BoundedLStarData.q013 3 1 ((BoundedLStarData.q013.core 3).edges 1) := by decide +kernel

private theorem q013_edge3_2 :
    EdgeChecks BoundedLStarData.q013 3 2 ((BoundedLStarData.q013.core 3).edges 2) := by decide +kernel

private theorem q013_edge3_3 :
    EdgeChecks BoundedLStarData.q013 3 3 ((BoundedLStarData.q013.core 3).edges 3) := by decide +kernel

private theorem q013_triangles3 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 3) = true := by decide +kernel

private theorem q013_descent3 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (-10) (6) (-2) (-2) (-1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable4 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 4).word) (BoundedLStarData.q013.node 4) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [1,3]) (ofSix (2) (-6) (2) (2) (1) (0))
  rw [q013_prefix4]
  intro u v; rfl

private theorem q013_cyclic4 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 4) := by decide +kernel

private theorem q013_edge4_0 :
    EdgeChecks BoundedLStarData.q013 4 0 ((BoundedLStarData.q013.core 4).edges 0) := by decide +kernel

private theorem q013_edge4_1 :
    EdgeChecks BoundedLStarData.q013 4 1 ((BoundedLStarData.q013.core 4).edges 1) := by decide +kernel

private theorem q013_edge4_2 :
    EdgeChecks BoundedLStarData.q013 4 2 ((BoundedLStarData.q013.core 4).edges 2) := by decide +kernel

private theorem q013_edge4_3 :
    EdgeChecks BoundedLStarData.q013 4 3 ((BoundedLStarData.q013.core 4).edges 3) := by decide +kernel

private theorem q013_triangles4 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 4) = true := by decide +kernel

private theorem q013_descent4 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-6) (2) (2) (1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable5 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 5).word) (BoundedLStarData.q013.node 5) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [3,1]) (ofSix (4) (-2) (-2) (0) (1) (2))
  rw [q013_prefix5]
  intro u v; rfl

private theorem q013_cyclic5 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 5) := by decide +kernel

private theorem q013_edge5_0 :
    EdgeChecks BoundedLStarData.q013 5 0 ((BoundedLStarData.q013.core 5).edges 0) := by decide +kernel

private theorem q013_edge5_1 :
    EdgeChecks BoundedLStarData.q013 5 1 ((BoundedLStarData.q013.core 5).edges 1) := by decide +kernel

private theorem q013_edge5_2 :
    EdgeChecks BoundedLStarData.q013 5 2 ((BoundedLStarData.q013.core 5).edges 2) := by decide +kernel

private theorem q013_edge5_3 :
    EdgeChecks BoundedLStarData.q013 5 3 ((BoundedLStarData.q013.core 5).edges 3) := by decide +kernel

private theorem q013_triangles5 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 5) = true := by decide +kernel

private theorem q013_descent5 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (4) (-2) (-2) (0) (1) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable6 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 6).word) (BoundedLStarData.q013.node 6) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [1,2,1]) (ofSix (10) (-14) (-12) (2) (1) (0))
  rw [q013_prefix6]
  intro u v; rfl

private theorem q013_cyclic6 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 6) := by decide +kernel

private theorem q013_edge6_0 :
    EdgeChecks BoundedLStarData.q013 6 0 ((BoundedLStarData.q013.core 6).edges 0) := by decide +kernel

private theorem q013_edge6_1 :
    EdgeChecks BoundedLStarData.q013 6 1 ((BoundedLStarData.q013.core 6).edges 1) := by decide +kernel

private theorem q013_edge6_2 :
    EdgeChecks BoundedLStarData.q013 6 2 ((BoundedLStarData.q013.core 6).edges 2) := by decide +kernel

private theorem q013_edge6_3 :
    EdgeChecks BoundedLStarData.q013 6 3 ((BoundedLStarData.q013.core 6).edges 3) := by decide +kernel

private theorem q013_triangles6 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 6) = true := by decide +kernel

private theorem q013_descent6 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (10) (-14) (-12) (2) (1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable7 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 7).word) (BoundedLStarData.q013.node 7) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [1,2,3]) (ofSix (-10) (6) (2) (-2) (1) (0))
  rw [q013_prefix7]
  intro u v; rfl

private theorem q013_cyclic7 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 7) := by decide +kernel

private theorem q013_edge7_0 :
    EdgeChecks BoundedLStarData.q013 7 0 ((BoundedLStarData.q013.core 7).edges 0) := by decide +kernel

private theorem q013_edge7_1 :
    EdgeChecks BoundedLStarData.q013 7 1 ((BoundedLStarData.q013.core 7).edges 1) := by decide +kernel

private theorem q013_edge7_2 :
    EdgeChecks BoundedLStarData.q013 7 2 ((BoundedLStarData.q013.core 7).edges 2) := by decide +kernel

private theorem q013_edge7_3 :
    EdgeChecks BoundedLStarData.q013 7 3 ((BoundedLStarData.q013.core 7).edges 3) := by decide +kernel

private theorem q013_triangles7 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 7) = true := by decide +kernel

private theorem q013_descent7 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (-10) (6) (2) (-2) (1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable8 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 8).word) (BoundedLStarData.q013.node 8) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [1,2,1,3]) (ofSix (-2) (-14) (12) (2) (-1) (0))
  rw [q013_prefix8]
  intro u v; rfl

private theorem q013_cyclic8 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 8) := by decide +kernel

private theorem q013_edge8_0 :
    EdgeChecks BoundedLStarData.q013 8 0 ((BoundedLStarData.q013.core 8).edges 0) := by decide +kernel

private theorem q013_edge8_1 :
    EdgeChecks BoundedLStarData.q013 8 1 ((BoundedLStarData.q013.core 8).edges 1) := by decide +kernel

private theorem q013_edge8_2 :
    EdgeChecks BoundedLStarData.q013 8 2 ((BoundedLStarData.q013.core 8).edges 2) := by decide +kernel

private theorem q013_edge8_3 :
    EdgeChecks BoundedLStarData.q013 8 3 ((BoundedLStarData.q013.core 8).edges 3) := by decide +kernel

private theorem q013_triangles8 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 8) = true := by decide +kernel

private theorem q013_descent8 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-14) (12) (2) (-1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q013_reachable9 :
    EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core 9).word) (BoundedLStarData.q013.node 9) := by
  change EntriesEqual (applyWord (BoundedLStarData.q013.node 0) [1,2,3,1]) (ofSix (10) (-14) (2) (2) (-1) (2))
  rw [q013_prefix9]
  intro u v; rfl

private theorem q013_cyclic9 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node 9) := by decide +kernel

private theorem q013_edge9_0 :
    EdgeChecks BoundedLStarData.q013 9 0 ((BoundedLStarData.q013.core 9).edges 0) := by decide +kernel

private theorem q013_edge9_1 :
    EdgeChecks BoundedLStarData.q013 9 1 ((BoundedLStarData.q013.core 9).edges 1) := by decide +kernel

private theorem q013_edge9_2 :
    EdgeChecks BoundedLStarData.q013 9 2 ((BoundedLStarData.q013.core 9).edges 2) := by decide +kernel

private theorem q013_edge9_3 :
    EdgeChecks BoundedLStarData.q013 9 3 ((BoundedLStarData.q013.core 9).edges 3) := by decide +kernel

private theorem q013_triangles9 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node 9) = true := by decide +kernel

private theorem q013_descent9 :
    allTriangleDescentsCheck (BoundedLStarData.q013.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (10) (-14) (2) (2) (-1) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem q013_reachable : ∀ i, EntriesEqual (applyWord (BoundedLStarData.q013.node 0) (BoundedLStarData.q013.core i).word) (BoundedLStarData.q013.node i) := by
  intro i
  change Fin 10 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q013_reachable0
  · exact q013_reachable1
  · exact q013_reachable2
  · exact q013_reachable3
  · exact q013_reachable4
  · exact q013_reachable5
  · exact q013_reachable6
  · exact q013_reachable7
  · exact q013_reachable8
  · exact q013_reachable9

theorem q013_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q013.node i) := by
  intro i
  change Fin 10 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q013_cyclic0
  · exact q013_cyclic1
  · exact q013_cyclic2
  · exact q013_cyclic3
  · exact q013_cyclic4
  · exact q013_cyclic5
  · exact q013_cyclic6
  · exact q013_cyclic7
  · exact q013_cyclic8
  · exact q013_cyclic9

theorem q013_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q013.node i) = true := by
  intro i
  change Fin 10 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q013_triangles0
  · exact q013_triangles1
  · exact q013_triangles2
  · exact q013_triangles3
  · exact q013_triangles4
  · exact q013_triangles5
  · exact q013_triangles6
  · exact q013_triangles7
  · exact q013_triangles8
  · exact q013_triangles9

theorem q013_descents : ∀ i, allTriangleDescentsCheck (BoundedLStarData.q013.node i) = true := by
  intro i
  change Fin 10 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q013_descent0
  · exact q013_descent1
  · exact q013_descent2
  · exact q013_descent3
  · exact q013_descent4
  · exact q013_descent5
  · exact q013_descent6
  · exact q013_descent7
  · exact q013_descent8
  · exact q013_descent9

theorem q013_edges : ∀ i k, EdgeChecks BoundedLStarData.q013 i k ((BoundedLStarData.q013.core i).edges k) := by
  intro i k
  change Fin 10 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge0_0
    · exact q013_edge0_1
    · exact q013_edge0_2
    · exact q013_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge1_0
    · exact q013_edge1_1
    · exact q013_edge1_2
    · exact q013_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge2_0
    · exact q013_edge2_1
    · exact q013_edge2_2
    · exact q013_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge3_0
    · exact q013_edge3_1
    · exact q013_edge3_2
    · exact q013_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge4_0
    · exact q013_edge4_1
    · exact q013_edge4_2
    · exact q013_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge5_0
    · exact q013_edge5_1
    · exact q013_edge5_2
    · exact q013_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge6_0
    · exact q013_edge6_1
    · exact q013_edge6_2
    · exact q013_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge7_0
    · exact q013_edge7_1
    · exact q013_edge7_2
    · exact q013_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge8_0
    · exact q013_edge8_1
    · exact q013_edge8_2
    · exact q013_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q013_edge9_0
    · exact q013_edge9_1
    · exact q013_edge9_2
    · exact q013_edge9_3

theorem q013_checks : Checks BoundedLStarData.q013 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := q013_reachable
  cyclic := q013_cyclic
  strips := by
    intro s
    change Fin 0 at s
    exact Fin.elim0 s
  edges := q013_edges
  triangles := (decide_eq_true q013_triangles).symm
  descents := fun _ => q013_descents

end QuiverProofs.BoundedLStarChecks
