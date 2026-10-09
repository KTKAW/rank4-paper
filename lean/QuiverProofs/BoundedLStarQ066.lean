import QuiverProofs.BoundedLStarData
import QuiverProofs.LStarCertificate
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem q066_prefix0 : applyWord (BoundedLStarData.q066.node 0) [] = (ofSix (-2) (-2) (-1) (-1) (1) (-1)) := by
  rfl

private theorem q066_prefix1 : applyWord (BoundedLStarData.q066.node 0) [1] = (ofSix (2) (-4) (-1) (1) (-1) (0)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,q066_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix2 : applyWord (BoundedLStarData.q066.node 0) [2] = (ofSix (-2) (2) (-3) (1) (0) (1)) := by
  rw [show ([2] : List (Fin 4)) = [] ++ [2] from rfl,
    applyWord_append,q066_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix3 : applyWord (BoundedLStarData.q066.node 0) [3] = (ofSix (-3) (-2) (1) (0) (-1) (1)) := by
  rw [show ([3] : List (Fin 4)) = [] ++ [3] from rfl,
    applyWord_append,q066_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix4 : applyWord (BoundedLStarData.q066.node 0) [1,0] = (ofSix (-2) (4) (1) (-7) (-3) (0)) := by
  rw [show ([1,0] : List (Fin 4)) = [1] ++ [0] from rfl,
    applyWord_append,q066_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix5 : applyWord (BoundedLStarData.q066.node 0) [1,2] = (ofSix (-2) (4) (-1) (-1) (-1) (0)) := by
  rw [show ([1,2] : List (Fin 4)) = [1] ++ [2] from rfl,
    applyWord_append,q066_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix6 : applyWord (BoundedLStarData.q066.node 0) [2,1] = (ofSix (2) (2) (-3) (-1) (0) (1)) := by
  rw [show ([2,1] : List (Fin 4)) = [2] ++ [1] from rfl,
    applyWord_append,q066_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix7 : applyWord (BoundedLStarData.q066.node 0) [2,3] = (ofSix (-2) (-1) (3) (1) (0) (-1)) := by
  rw [show ([2,3] : List (Fin 4)) = [2] ++ [3] from rfl,
    applyWord_append,q066_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix8 : applyWord (BoundedLStarData.q066.node 0) [3,0] = (ofSix (3) (2) (-1) (0) (2) (3)) := by
  rw [show ([3,0] : List (Fin 4)) = [3] ++ [0] from rfl,
    applyWord_append,q066_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix9 : applyWord (BoundedLStarData.q066.node 0) [1,0,3] = (ofSix (1) (4) (-1) (-7) (3) (0)) := by
  rw [show ([1,0,3] : List (Fin 4)) = [1,0] ++ [3] from rfl,
    applyWord_append,q066_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix10 : applyWord (BoundedLStarData.q066.node 0) [1,2,0] = (ofSix (2) (-4) (1) (7) (-1) (-4)) := by
  rw [show ([1,2,0] : List (Fin 4)) = [1,2] ++ [0] from rfl,
    applyWord_append,q066_prefix5]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix11 : applyWord (BoundedLStarData.q066.node 0) [2,3,0] = (ofSix (2) (1) (-3) (1) (6) (2)) := by
  rw [show ([2,3,0] : List (Fin 4)) = [2,3] ++ [0] from rfl,
    applyWord_append,q066_prefix7]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix12 : applyWord (BoundedLStarData.q066.node 0) [3,0,1] = (ofSix (-3) (2) (5) (0) (-2) (3)) := by
  rw [show ([3,0,1] : List (Fin 4)) = [3,0] ++ [1] from rfl,
    applyWord_append,q066_prefix8]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix13 : applyWord (BoundedLStarData.q066.node 0) [1,0,3,1] = (ofSix (-1) (4) (2) (7) (-3) (21)) := by
  rw [show ([1,0,3,1] : List (Fin 4)) = [1,0,3] ++ [1] from rfl,
    applyWord_append,q066_prefix9]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix14 : applyWord (BoundedLStarData.q066.node 0) [1,2,0,1] = (ofSix (-2) (10) (1) (-7) (1) (-11)) := by
  rw [show ([1,2,0,1] : List (Fin 4)) = [1,2,0] ++ [1] from rfl,
    applyWord_append,q066_prefix10]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix15 : applyWord (BoundedLStarData.q066.node 0) [2,3,0,1] = (ofSix (-2) (3) (9) (-1) (-6) (2)) := by
  rw [show ([2,3,0,1] : List (Fin 4)) = [2,3,0] ++ [1] from rfl,
    applyWord_append,q066_prefix11]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix16 : applyWord (BoundedLStarData.q066.node 0) [2,3,0,2] = (ofSix (2) (-1) (-1) (-1) (8) (-2)) := by
  rw [show ([2,3,0,2] : List (Fin 4)) = [2,3,0] ++ [2] from rfl,
    applyWord_append,q066_prefix11]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix17 : applyWord (BoundedLStarData.q066.node 0) [3,0,1,2] = (ofSix (-3) (-2) (11) (0) (-2) (-3)) := by
  rw [show ([3,0,1,2] : List (Fin 4)) = [3,0,1] ++ [2] from rfl,
    applyWord_append,q066_prefix12]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix18 : applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0] = (ofSix (1) (-4) (-2) (11) (-1) (21)) := by
  rw [show ([1,0,3,1,0] : List (Fin 4)) = [1,0,3,1] ++ [0] from rfl,
    applyWord_append,q066_prefix13]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix19 : applyWord (BoundedLStarData.q066.node 0) [1,2,0,1,0] = (ofSix (2) (-10) (-1) (13) (3) (-11)) := by
  rw [show ([1,2,0,1,0] : List (Fin 4)) = [1,2,0,1] ++ [0] from rfl,
    applyWord_append,q066_prefix14]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix20 : applyWord (BoundedLStarData.q066.node 0) [2,3,0,1,2] = (ofSix (1) (-3) (15) (1) (-6) (-2)) := by
  rw [show ([2,3,0,1,2] : List (Fin 4)) = [2,3,0,1] ++ [2] from rfl,
    applyWord_append,q066_prefix15]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix21 : applyWord (BoundedLStarData.q066.node 0) [2,3,0,2,1] = (ofSix (-2) (-1) (15) (1) (-8) (6)) := by
  rw [show ([2,3,0,2,1] : List (Fin 4)) = [2,3,0,2] ++ [1] from rfl,
    applyWord_append,q066_prefix16]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix22 : applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0,3] = (ofSix (1) (-46) (2) (-10) (1) (-21)) := by
  rw [show ([1,0,3,1,0,3] : List (Fin 4)) = [1,0,3,1,0] ++ [3] from rfl,
    applyWord_append,q066_prefix18]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix23 : applyWord (BoundedLStarData.q066.node 0) [1,2,0,1,0,3] = (ofSix (-1) (-10) (1) (46) (-3) (11)) := by
  rw [show ([1,2,0,1,0,3] : List (Fin 4)) = [1,2,0,1,0] ++ [3] from rfl,
    applyWord_append,q066_prefix19]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix24 : applyWord (BoundedLStarData.q066.node 0) [2,3,0,1,2,0] = (ofSix (-1) (3) (-15) (-2) (-6) (43)) := by
  rw [show ([2,3,0,1,2,0] : List (Fin 4)) = [2,3,0,1,2] ++ [0] from rfl,
    applyWord_append,q066_prefix20]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix25 : applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0,3,0] = (ofSix (-1) (46) (-2) (-56) (1) (71)) := by
  rw [show ([1,0,3,1,0,3,0] : List (Fin 4)) = [1,0,3,1,0,3] ++ [0] from rfl,
    applyWord_append,q066_prefix22]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix26 : applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0,3,0,1] = (ofSix (1) (-10) (-2) (56) (-1) (127)) := by
  rw [show ([1,0,3,1,0,3,0,1] : List (Fin 4)) = [1,0,3,1,0,3,0] ++ [1] from rfl,
    applyWord_append,q066_prefix25]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_prefix27 : applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0,3,0,1,0] = (ofSix (-1) (10) (2) (46) (-3) (127)) := by
  rw [show ([1,0,3,1,0,3,0,1,0] : List (Fin 4)) = [1,0,3,1,0,3,0,1] ++ [0] from rfl,
    applyWord_append,q066_prefix26]
  apply entriesEqual_eq
  decide +kernel

private theorem q066_reachable0 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 0).word) (BoundedLStarData.q066.node 0) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) []) (ofSix (-2) (-2) (-1) (-1) (1) (-1))
  rw [q066_prefix0]
  intro u v; rfl

private theorem q066_cyclic0 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 0) := by decide +kernel

private theorem q066_edge0_0 :
    EdgeChecks BoundedLStarData.q066 0 0 ((BoundedLStarData.q066.core 0).edges 0) := by decide +kernel

private theorem q066_edge0_1 :
    EdgeChecks BoundedLStarData.q066 0 1 ((BoundedLStarData.q066.core 0).edges 1) := by decide +kernel

private theorem q066_edge0_2 :
    EdgeChecks BoundedLStarData.q066 0 2 ((BoundedLStarData.q066.core 0).edges 2) := by decide +kernel

private theorem q066_edge0_3 :
    EdgeChecks BoundedLStarData.q066 0 3 ((BoundedLStarData.q066.core 0).edges 3) := by decide +kernel

private theorem q066_triangles0 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 0) = true := by decide +kernel

private theorem q066_descent0 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-2) (-1) (-1) (1) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable1 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 1).word) (BoundedLStarData.q066.node 1) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1]) (ofSix (2) (-4) (-1) (1) (-1) (0))
  rw [q066_prefix1]
  intro u v; rfl

private theorem q066_cyclic1 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 1) := by decide +kernel

private theorem q066_edge1_0 :
    EdgeChecks BoundedLStarData.q066 1 0 ((BoundedLStarData.q066.core 1).edges 0) := by decide +kernel

private theorem q066_edge1_1 :
    EdgeChecks BoundedLStarData.q066 1 1 ((BoundedLStarData.q066.core 1).edges 1) := by decide +kernel

private theorem q066_edge1_2 :
    EdgeChecks BoundedLStarData.q066 1 2 ((BoundedLStarData.q066.core 1).edges 2) := by decide +kernel

private theorem q066_edge1_3 :
    EdgeChecks BoundedLStarData.q066 1 3 ((BoundedLStarData.q066.core 1).edges 3) := by decide +kernel

private theorem q066_triangles1 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 1) = true := by decide +kernel

private theorem q066_descent1 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-4) (-1) (1) (-1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable2 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 2).word) (BoundedLStarData.q066.node 2) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2]) (ofSix (-2) (2) (-3) (1) (0) (1))
  rw [q066_prefix2]
  intro u v; rfl

private theorem q066_cyclic2 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 2) := by decide +kernel

private theorem q066_edge2_0 :
    EdgeChecks BoundedLStarData.q066 2 0 ((BoundedLStarData.q066.core 2).edges 0) := by decide +kernel

private theorem q066_edge2_1 :
    EdgeChecks BoundedLStarData.q066 2 1 ((BoundedLStarData.q066.core 2).edges 1) := by decide +kernel

private theorem q066_edge2_2 :
    EdgeChecks BoundedLStarData.q066 2 2 ((BoundedLStarData.q066.core 2).edges 2) := by decide +kernel

private theorem q066_edge2_3 :
    EdgeChecks BoundedLStarData.q066 2 3 ((BoundedLStarData.q066.core 2).edges 3) := by decide +kernel

private theorem q066_triangles2 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 2) = true := by decide +kernel

private theorem q066_descent2 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (2) (-3) (1) (0) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable3 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 3).word) (BoundedLStarData.q066.node 3) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [3]) (ofSix (-3) (-2) (1) (0) (-1) (1))
  rw [q066_prefix3]
  intro u v; rfl

private theorem q066_cyclic3 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 3) := by decide +kernel

private theorem q066_edge3_0 :
    EdgeChecks BoundedLStarData.q066 3 0 ((BoundedLStarData.q066.core 3).edges 0) := by decide +kernel

private theorem q066_edge3_1 :
    EdgeChecks BoundedLStarData.q066 3 1 ((BoundedLStarData.q066.core 3).edges 1) := by decide +kernel

private theorem q066_edge3_2 :
    EdgeChecks BoundedLStarData.q066 3 2 ((BoundedLStarData.q066.core 3).edges 2) := by decide +kernel

private theorem q066_edge3_3 :
    EdgeChecks BoundedLStarData.q066 3 3 ((BoundedLStarData.q066.core 3).edges 3) := by decide +kernel

private theorem q066_triangles3 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 3) = true := by decide +kernel

private theorem q066_descent3 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (-3) (-2) (1) (0) (-1) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable4 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 4).word) (BoundedLStarData.q066.node 4) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,0]) (ofSix (-2) (4) (1) (-7) (-3) (0))
  rw [q066_prefix4]
  intro u v; rfl

private theorem q066_cyclic4 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 4) := by decide +kernel

private theorem q066_edge4_0 :
    EdgeChecks BoundedLStarData.q066 4 0 ((BoundedLStarData.q066.core 4).edges 0) := by decide +kernel

private theorem q066_edge4_1 :
    EdgeChecks BoundedLStarData.q066 4 1 ((BoundedLStarData.q066.core 4).edges 1) := by decide +kernel

private theorem q066_edge4_2 :
    EdgeChecks BoundedLStarData.q066 4 2 ((BoundedLStarData.q066.core 4).edges 2) := by decide +kernel

private theorem q066_edge4_3 :
    EdgeChecks BoundedLStarData.q066 4 3 ((BoundedLStarData.q066.core 4).edges 3) := by decide +kernel

private theorem q066_triangles4 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 4) = true := by decide +kernel

private theorem q066_descent4 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (4) (1) (-7) (-3) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable5 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 5).word) (BoundedLStarData.q066.node 5) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,2]) (ofSix (-2) (4) (-1) (-1) (-1) (0))
  rw [q066_prefix5]
  intro u v; rfl

private theorem q066_cyclic5 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 5) := by decide +kernel

private theorem q066_edge5_0 :
    EdgeChecks BoundedLStarData.q066 5 0 ((BoundedLStarData.q066.core 5).edges 0) := by decide +kernel

private theorem q066_edge5_1 :
    EdgeChecks BoundedLStarData.q066 5 1 ((BoundedLStarData.q066.core 5).edges 1) := by decide +kernel

private theorem q066_edge5_2 :
    EdgeChecks BoundedLStarData.q066 5 2 ((BoundedLStarData.q066.core 5).edges 2) := by decide +kernel

private theorem q066_edge5_3 :
    EdgeChecks BoundedLStarData.q066 5 3 ((BoundedLStarData.q066.core 5).edges 3) := by decide +kernel

private theorem q066_triangles5 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 5) = true := by decide +kernel

private theorem q066_descent5 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (4) (-1) (-1) (-1) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable6 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 6).word) (BoundedLStarData.q066.node 6) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,1]) (ofSix (2) (2) (-3) (-1) (0) (1))
  rw [q066_prefix6]
  intro u v; rfl

private theorem q066_cyclic6 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 6) := by decide +kernel

private theorem q066_edge6_0 :
    EdgeChecks BoundedLStarData.q066 6 0 ((BoundedLStarData.q066.core 6).edges 0) := by decide +kernel

private theorem q066_edge6_1 :
    EdgeChecks BoundedLStarData.q066 6 1 ((BoundedLStarData.q066.core 6).edges 1) := by decide +kernel

private theorem q066_edge6_2 :
    EdgeChecks BoundedLStarData.q066 6 2 ((BoundedLStarData.q066.core 6).edges 2) := by decide +kernel

private theorem q066_edge6_3 :
    EdgeChecks BoundedLStarData.q066 6 3 ((BoundedLStarData.q066.core 6).edges 3) := by decide +kernel

private theorem q066_triangles6 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 6) = true := by decide +kernel

private theorem q066_descent6 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (2) (2) (-3) (-1) (0) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable7 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 7).word) (BoundedLStarData.q066.node 7) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3]) (ofSix (-2) (-1) (3) (1) (0) (-1))
  rw [q066_prefix7]
  intro u v; rfl

private theorem q066_cyclic7 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 7) := by decide +kernel

private theorem q066_edge7_0 :
    EdgeChecks BoundedLStarData.q066 7 0 ((BoundedLStarData.q066.core 7).edges 0) := by decide +kernel

private theorem q066_edge7_1 :
    EdgeChecks BoundedLStarData.q066 7 1 ((BoundedLStarData.q066.core 7).edges 1) := by decide +kernel

private theorem q066_edge7_2 :
    EdgeChecks BoundedLStarData.q066 7 2 ((BoundedLStarData.q066.core 7).edges 2) := by decide +kernel

private theorem q066_edge7_3 :
    EdgeChecks BoundedLStarData.q066 7 3 ((BoundedLStarData.q066.core 7).edges 3) := by decide +kernel

private theorem q066_triangles7 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 7) = true := by decide +kernel

private theorem q066_descent7 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-1) (3) (1) (0) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable8 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 8).word) (BoundedLStarData.q066.node 8) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [3,0]) (ofSix (3) (2) (-1) (0) (2) (3))
  rw [q066_prefix8]
  intro u v; rfl

private theorem q066_cyclic8 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 8) := by decide +kernel

private theorem q066_edge8_0 :
    EdgeChecks BoundedLStarData.q066 8 0 ((BoundedLStarData.q066.core 8).edges 0) := by decide +kernel

private theorem q066_edge8_1 :
    EdgeChecks BoundedLStarData.q066 8 1 ((BoundedLStarData.q066.core 8).edges 1) := by decide +kernel

private theorem q066_edge8_2 :
    EdgeChecks BoundedLStarData.q066 8 2 ((BoundedLStarData.q066.core 8).edges 2) := by decide +kernel

private theorem q066_edge8_3 :
    EdgeChecks BoundedLStarData.q066 8 3 ((BoundedLStarData.q066.core 8).edges 3) := by decide +kernel

private theorem q066_triangles8 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 8) = true := by decide +kernel

private theorem q066_descent8 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (3) (2) (-1) (0) (2) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable9 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 9).word) (BoundedLStarData.q066.node 9) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,0,3]) (ofSix (1) (4) (-1) (-7) (3) (0))
  rw [q066_prefix9]
  intro u v; rfl

private theorem q066_cyclic9 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 9) := by decide +kernel

private theorem q066_edge9_0 :
    EdgeChecks BoundedLStarData.q066 9 0 ((BoundedLStarData.q066.core 9).edges 0) := by decide +kernel

private theorem q066_edge9_1 :
    EdgeChecks BoundedLStarData.q066 9 1 ((BoundedLStarData.q066.core 9).edges 1) := by decide +kernel

private theorem q066_edge9_2 :
    EdgeChecks BoundedLStarData.q066 9 2 ((BoundedLStarData.q066.core 9).edges 2) := by decide +kernel

private theorem q066_edge9_3 :
    EdgeChecks BoundedLStarData.q066 9 3 ((BoundedLStarData.q066.core 9).edges 3) := by decide +kernel

private theorem q066_triangles9 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 9) = true := by decide +kernel

private theorem q066_descent9 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (1) (4) (-1) (-7) (3) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable10 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 10).word) (BoundedLStarData.q066.node 10) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,2,0]) (ofSix (2) (-4) (1) (7) (-1) (-4))
  rw [q066_prefix10]
  intro u v; rfl

private theorem q066_cyclic10 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 10) := by decide +kernel

private theorem q066_edge10_0 :
    EdgeChecks BoundedLStarData.q066 10 0 ((BoundedLStarData.q066.core 10).edges 0) := by decide +kernel

private theorem q066_edge10_1 :
    EdgeChecks BoundedLStarData.q066 10 1 ((BoundedLStarData.q066.core 10).edges 1) := by decide +kernel

private theorem q066_edge10_2 :
    EdgeChecks BoundedLStarData.q066 10 2 ((BoundedLStarData.q066.core 10).edges 2) := by decide +kernel

private theorem q066_edge10_3 :
    EdgeChecks BoundedLStarData.q066 10 3 ((BoundedLStarData.q066.core 10).edges 3) := by decide +kernel

private theorem q066_triangles10 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 10) = true := by decide +kernel

private theorem q066_descent10 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 10) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-4) (1) (7) (-1) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable11 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 11).word) (BoundedLStarData.q066.node 11) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3,0]) (ofSix (2) (1) (-3) (1) (6) (2))
  rw [q066_prefix11]
  intro u v; rfl

private theorem q066_cyclic11 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 11) := by decide +kernel

private theorem q066_edge11_0 :
    EdgeChecks BoundedLStarData.q066 11 0 ((BoundedLStarData.q066.core 11).edges 0) := by decide +kernel

private theorem q066_edge11_1 :
    EdgeChecks BoundedLStarData.q066 11 1 ((BoundedLStarData.q066.core 11).edges 1) := by decide +kernel

private theorem q066_edge11_2 :
    EdgeChecks BoundedLStarData.q066 11 2 ((BoundedLStarData.q066.core 11).edges 2) := by decide +kernel

private theorem q066_edge11_3 :
    EdgeChecks BoundedLStarData.q066 11 3 ((BoundedLStarData.q066.core 11).edges 3) := by decide +kernel

private theorem q066_triangles11 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 11) = true := by decide +kernel

private theorem q066_descent11 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 11) = true := by
  change allTriangleDescentsCheck (ofSix (2) (1) (-3) (1) (6) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable12 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 12).word) (BoundedLStarData.q066.node 12) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [3,0,1]) (ofSix (-3) (2) (5) (0) (-2) (3))
  rw [q066_prefix12]
  intro u v; rfl

private theorem q066_cyclic12 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 12) := by decide +kernel

private theorem q066_edge12_0 :
    EdgeChecks BoundedLStarData.q066 12 0 ((BoundedLStarData.q066.core 12).edges 0) := by decide +kernel

private theorem q066_edge12_1 :
    EdgeChecks BoundedLStarData.q066 12 1 ((BoundedLStarData.q066.core 12).edges 1) := by decide +kernel

private theorem q066_edge12_2 :
    EdgeChecks BoundedLStarData.q066 12 2 ((BoundedLStarData.q066.core 12).edges 2) := by decide +kernel

private theorem q066_edge12_3 :
    EdgeChecks BoundedLStarData.q066 12 3 ((BoundedLStarData.q066.core 12).edges 3) := by decide +kernel

private theorem q066_triangles12 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 12) = true := by decide +kernel

private theorem q066_descent12 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 12) = true := by
  change allTriangleDescentsCheck (ofSix (-3) (2) (5) (0) (-2) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable13 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 13).word) (BoundedLStarData.q066.node 13) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,0,3,1]) (ofSix (-1) (4) (2) (7) (-3) (21))
  rw [q066_prefix13]
  intro u v; rfl

private theorem q066_cyclic13 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 13) := by decide +kernel

private theorem q066_edge13_0 :
    EdgeChecks BoundedLStarData.q066 13 0 ((BoundedLStarData.q066.core 13).edges 0) := by decide +kernel

private theorem q066_edge13_1 :
    EdgeChecks BoundedLStarData.q066 13 1 ((BoundedLStarData.q066.core 13).edges 1) := by decide +kernel

private theorem q066_edge13_2 :
    EdgeChecks BoundedLStarData.q066 13 2 ((BoundedLStarData.q066.core 13).edges 2) := by decide +kernel

private theorem q066_edge13_3 :
    EdgeChecks BoundedLStarData.q066 13 3 ((BoundedLStarData.q066.core 13).edges 3) := by decide +kernel

private theorem q066_triangles13 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 13) = true := by decide +kernel

private theorem q066_descent13 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 13) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (4) (2) (7) (-3) (21)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable14 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 14).word) (BoundedLStarData.q066.node 14) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,2,0,1]) (ofSix (-2) (10) (1) (-7) (1) (-11))
  rw [q066_prefix14]
  intro u v; rfl

private theorem q066_cyclic14 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 14) := by decide +kernel

private theorem q066_edge14_0 :
    EdgeChecks BoundedLStarData.q066 14 0 ((BoundedLStarData.q066.core 14).edges 0) := by decide +kernel

private theorem q066_edge14_1 :
    EdgeChecks BoundedLStarData.q066 14 1 ((BoundedLStarData.q066.core 14).edges 1) := by decide +kernel

private theorem q066_edge14_2 :
    EdgeChecks BoundedLStarData.q066 14 2 ((BoundedLStarData.q066.core 14).edges 2) := by decide +kernel

private theorem q066_edge14_3 :
    EdgeChecks BoundedLStarData.q066 14 3 ((BoundedLStarData.q066.core 14).edges 3) := by decide +kernel

private theorem q066_triangles14 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 14) = true := by decide +kernel

private theorem q066_descent14 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 14) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (10) (1) (-7) (1) (-11)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable15 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 15).word) (BoundedLStarData.q066.node 15) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3,0,1]) (ofSix (-2) (3) (9) (-1) (-6) (2))
  rw [q066_prefix15]
  intro u v; rfl

private theorem q066_cyclic15 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 15) := by decide +kernel

private theorem q066_edge15_0 :
    EdgeChecks BoundedLStarData.q066 15 0 ((BoundedLStarData.q066.core 15).edges 0) := by decide +kernel

private theorem q066_edge15_1 :
    EdgeChecks BoundedLStarData.q066 15 1 ((BoundedLStarData.q066.core 15).edges 1) := by decide +kernel

private theorem q066_edge15_2 :
    EdgeChecks BoundedLStarData.q066 15 2 ((BoundedLStarData.q066.core 15).edges 2) := by decide +kernel

private theorem q066_edge15_3 :
    EdgeChecks BoundedLStarData.q066 15 3 ((BoundedLStarData.q066.core 15).edges 3) := by decide +kernel

private theorem q066_triangles15 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 15) = true := by decide +kernel

private theorem q066_descent15 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 15) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (3) (9) (-1) (-6) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable16 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 16).word) (BoundedLStarData.q066.node 16) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3,0,2]) (ofSix (2) (-1) (-1) (-1) (8) (-2))
  rw [q066_prefix16]
  intro u v; rfl

private theorem q066_cyclic16 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 16) := by decide +kernel

private theorem q066_edge16_0 :
    EdgeChecks BoundedLStarData.q066 16 0 ((BoundedLStarData.q066.core 16).edges 0) := by decide +kernel

private theorem q066_edge16_1 :
    EdgeChecks BoundedLStarData.q066 16 1 ((BoundedLStarData.q066.core 16).edges 1) := by decide +kernel

private theorem q066_edge16_2 :
    EdgeChecks BoundedLStarData.q066 16 2 ((BoundedLStarData.q066.core 16).edges 2) := by decide +kernel

private theorem q066_edge16_3 :
    EdgeChecks BoundedLStarData.q066 16 3 ((BoundedLStarData.q066.core 16).edges 3) := by decide +kernel

private theorem q066_triangles16 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 16) = true := by decide +kernel

private theorem q066_descent16 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 16) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (-1) (-1) (8) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable17 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 17).word) (BoundedLStarData.q066.node 17) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [3,0,1,2]) (ofSix (-3) (-2) (11) (0) (-2) (-3))
  rw [q066_prefix17]
  intro u v; rfl

private theorem q066_cyclic17 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 17) := by decide +kernel

private theorem q066_edge17_0 :
    EdgeChecks BoundedLStarData.q066 17 0 ((BoundedLStarData.q066.core 17).edges 0) := by decide +kernel

private theorem q066_edge17_1 :
    EdgeChecks BoundedLStarData.q066 17 1 ((BoundedLStarData.q066.core 17).edges 1) := by decide +kernel

private theorem q066_edge17_2 :
    EdgeChecks BoundedLStarData.q066 17 2 ((BoundedLStarData.q066.core 17).edges 2) := by decide +kernel

private theorem q066_edge17_3 :
    EdgeChecks BoundedLStarData.q066 17 3 ((BoundedLStarData.q066.core 17).edges 3) := by decide +kernel

private theorem q066_triangles17 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 17) = true := by decide +kernel

private theorem q066_descent17 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 17) = true := by
  change allTriangleDescentsCheck (ofSix (-3) (-2) (11) (0) (-2) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable18 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 18).word) (BoundedLStarData.q066.node 18) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0]) (ofSix (1) (-4) (-2) (11) (-1) (21))
  rw [q066_prefix18]
  intro u v; rfl

private theorem q066_cyclic18 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 18) := by decide +kernel

private theorem q066_edge18_0 :
    EdgeChecks BoundedLStarData.q066 18 0 ((BoundedLStarData.q066.core 18).edges 0) := by decide +kernel

private theorem q066_edge18_1 :
    EdgeChecks BoundedLStarData.q066 18 1 ((BoundedLStarData.q066.core 18).edges 1) := by decide +kernel

private theorem q066_edge18_2 :
    EdgeChecks BoundedLStarData.q066 18 2 ((BoundedLStarData.q066.core 18).edges 2) := by decide +kernel

private theorem q066_edge18_3 :
    EdgeChecks BoundedLStarData.q066 18 3 ((BoundedLStarData.q066.core 18).edges 3) := by decide +kernel

private theorem q066_triangles18 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 18) = true := by decide +kernel

private theorem q066_descent18 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 18) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-4) (-2) (11) (-1) (21)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable19 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 19).word) (BoundedLStarData.q066.node 19) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,2,0,1,0]) (ofSix (2) (-10) (-1) (13) (3) (-11))
  rw [q066_prefix19]
  intro u v; rfl

private theorem q066_cyclic19 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 19) := by decide +kernel

private theorem q066_edge19_0 :
    EdgeChecks BoundedLStarData.q066 19 0 ((BoundedLStarData.q066.core 19).edges 0) := by decide +kernel

private theorem q066_edge19_1 :
    EdgeChecks BoundedLStarData.q066 19 1 ((BoundedLStarData.q066.core 19).edges 1) := by decide +kernel

private theorem q066_edge19_2 :
    EdgeChecks BoundedLStarData.q066 19 2 ((BoundedLStarData.q066.core 19).edges 2) := by decide +kernel

private theorem q066_edge19_3 :
    EdgeChecks BoundedLStarData.q066 19 3 ((BoundedLStarData.q066.core 19).edges 3) := by decide +kernel

private theorem q066_triangles19 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 19) = true := by decide +kernel

private theorem q066_descent19 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 19) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-10) (-1) (13) (3) (-11)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable20 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 20).word) (BoundedLStarData.q066.node 20) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3,0,1,2]) (ofSix (1) (-3) (15) (1) (-6) (-2))
  rw [q066_prefix20]
  intro u v; rfl

private theorem q066_cyclic20 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 20) := by decide +kernel

private theorem q066_edge20_0 :
    EdgeChecks BoundedLStarData.q066 20 0 ((BoundedLStarData.q066.core 20).edges 0) := by decide +kernel

private theorem q066_edge20_1 :
    EdgeChecks BoundedLStarData.q066 20 1 ((BoundedLStarData.q066.core 20).edges 1) := by decide +kernel

private theorem q066_edge20_2 :
    EdgeChecks BoundedLStarData.q066 20 2 ((BoundedLStarData.q066.core 20).edges 2) := by decide +kernel

private theorem q066_edge20_3 :
    EdgeChecks BoundedLStarData.q066 20 3 ((BoundedLStarData.q066.core 20).edges 3) := by decide +kernel

private theorem q066_triangles20 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 20) = true := by decide +kernel

private theorem q066_descent20 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 20) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-3) (15) (1) (-6) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable21 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 21).word) (BoundedLStarData.q066.node 21) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3,0,2,1]) (ofSix (-2) (-1) (15) (1) (-8) (6))
  rw [q066_prefix21]
  intro u v; rfl

private theorem q066_cyclic21 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 21) := by decide +kernel

private theorem q066_edge21_0 :
    EdgeChecks BoundedLStarData.q066 21 0 ((BoundedLStarData.q066.core 21).edges 0) := by decide +kernel

private theorem q066_edge21_1 :
    EdgeChecks BoundedLStarData.q066 21 1 ((BoundedLStarData.q066.core 21).edges 1) := by decide +kernel

private theorem q066_edge21_2 :
    EdgeChecks BoundedLStarData.q066 21 2 ((BoundedLStarData.q066.core 21).edges 2) := by decide +kernel

private theorem q066_edge21_3 :
    EdgeChecks BoundedLStarData.q066 21 3 ((BoundedLStarData.q066.core 21).edges 3) := by decide +kernel

private theorem q066_triangles21 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 21) = true := by decide +kernel

private theorem q066_descent21 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 21) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-1) (15) (1) (-8) (6)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable22 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 22).word) (BoundedLStarData.q066.node 22) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0,3]) (ofSix (1) (-46) (2) (-10) (1) (-21))
  rw [q066_prefix22]
  intro u v; rfl

private theorem q066_cyclic22 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 22) := by decide +kernel

private theorem q066_edge22_0 :
    EdgeChecks BoundedLStarData.q066 22 0 ((BoundedLStarData.q066.core 22).edges 0) := by decide +kernel

private theorem q066_edge22_1 :
    EdgeChecks BoundedLStarData.q066 22 1 ((BoundedLStarData.q066.core 22).edges 1) := by decide +kernel

private theorem q066_edge22_2 :
    EdgeChecks BoundedLStarData.q066 22 2 ((BoundedLStarData.q066.core 22).edges 2) := by decide +kernel

private theorem q066_edge22_3 :
    EdgeChecks BoundedLStarData.q066 22 3 ((BoundedLStarData.q066.core 22).edges 3) := by decide +kernel

private theorem q066_triangles22 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 22) = true := by decide +kernel

private theorem q066_descent22 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 22) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-46) (2) (-10) (1) (-21)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable23 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 23).word) (BoundedLStarData.q066.node 23) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,2,0,1,0,3]) (ofSix (-1) (-10) (1) (46) (-3) (11))
  rw [q066_prefix23]
  intro u v; rfl

private theorem q066_cyclic23 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 23) := by decide +kernel

private theorem q066_edge23_0 :
    EdgeChecks BoundedLStarData.q066 23 0 ((BoundedLStarData.q066.core 23).edges 0) := by decide +kernel

private theorem q066_edge23_1 :
    EdgeChecks BoundedLStarData.q066 23 1 ((BoundedLStarData.q066.core 23).edges 1) := by decide +kernel

private theorem q066_edge23_2 :
    EdgeChecks BoundedLStarData.q066 23 2 ((BoundedLStarData.q066.core 23).edges 2) := by decide +kernel

private theorem q066_edge23_3 :
    EdgeChecks BoundedLStarData.q066 23 3 ((BoundedLStarData.q066.core 23).edges 3) := by decide +kernel

private theorem q066_triangles23 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 23) = true := by decide +kernel

private theorem q066_descent23 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 23) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (-10) (1) (46) (-3) (11)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable24 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 24).word) (BoundedLStarData.q066.node 24) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3,0,1,2,0]) (ofSix (-1) (3) (-15) (-2) (-6) (43))
  rw [q066_prefix24]
  intro u v; rfl

private theorem q066_cyclic24 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 24) := by decide +kernel

private theorem q066_edge24_0 :
    EdgeChecks BoundedLStarData.q066 24 0 ((BoundedLStarData.q066.core 24).edges 0) := by decide +kernel

private theorem q066_edge24_1 :
    EdgeChecks BoundedLStarData.q066 24 1 ((BoundedLStarData.q066.core 24).edges 1) := by decide +kernel

private theorem q066_edge24_2 :
    EdgeChecks BoundedLStarData.q066 24 2 ((BoundedLStarData.q066.core 24).edges 2) := by decide +kernel

private theorem q066_edge24_3 :
    EdgeChecks BoundedLStarData.q066 24 3 ((BoundedLStarData.q066.core 24).edges 3) := by decide +kernel

private theorem q066_triangles24 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 24) = true := by decide +kernel

private theorem q066_descent24 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 24) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (3) (-15) (-2) (-6) (43)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_reachable25 :
    EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core 25).word) (BoundedLStarData.q066.node 25) := by
  change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0,3,0,1,0]) (ofSix (-1) (10) (2) (46) (-3) (127))
  rw [q066_prefix27]
  intro u v; rfl

private theorem q066_cyclic25 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node 25) := by decide +kernel

private theorem q066_edge25_0 :
    EdgeChecks BoundedLStarData.q066 25 0 ((BoundedLStarData.q066.core 25).edges 0) := by decide +kernel

private theorem q066_edge25_1 :
    EdgeChecks BoundedLStarData.q066 25 1 ((BoundedLStarData.q066.core 25).edges 1) := by decide +kernel

private theorem q066_edge25_2 :
    EdgeChecks BoundedLStarData.q066 25 2 ((BoundedLStarData.q066.core 25).edges 2) := by decide +kernel

private theorem q066_edge25_3 :
    EdgeChecks BoundedLStarData.q066 25 3 ((BoundedLStarData.q066.core 25).edges 3) := by decide +kernel

private theorem q066_triangles25 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node 25) = true := by decide +kernel

private theorem q066_descent25 :
    allTriangleDescentsCheck (BoundedLStarData.q066.node 25) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (10) (2) (46) (-3) (127)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q066_strip0 : StripChecks BoundedLStarData.q066 (BoundedLStarData.q066.strips (0 : Fin 2)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [2,3,0,2,1]) (BoundedLStarData.q066.node 21)
    rw [q066_prefix21]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

private theorem q066_strip1 : StripChecks BoundedLStarData.q066 (BoundedLStarData.q066.strips (1 : Fin 2)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (BoundedLStarData.q066.node 0) [1,0,3,1,0,3]) (BoundedLStarData.q066.node 22)
    rw [q066_prefix22]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

theorem q066_reachable : ∀ i, EntriesEqual (applyWord (BoundedLStarData.q066.node 0) (BoundedLStarData.q066.core i).word) (BoundedLStarData.q066.node i) := by
  intro i
  change Fin 26 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q066_reachable0
  · exact q066_reachable1
  · exact q066_reachable2
  · exact q066_reachable3
  · exact q066_reachable4
  · exact q066_reachable5
  · exact q066_reachable6
  · exact q066_reachable7
  · exact q066_reachable8
  · exact q066_reachable9
  · exact q066_reachable10
  · exact q066_reachable11
  · exact q066_reachable12
  · exact q066_reachable13
  · exact q066_reachable14
  · exact q066_reachable15
  · exact q066_reachable16
  · exact q066_reachable17
  · exact q066_reachable18
  · exact q066_reachable19
  · exact q066_reachable20
  · exact q066_reachable21
  · exact q066_reachable22
  · exact q066_reachable23
  · exact q066_reachable24
  · exact q066_reachable25

theorem q066_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q066.node i) := by
  intro i
  change Fin 26 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q066_cyclic0
  · exact q066_cyclic1
  · exact q066_cyclic2
  · exact q066_cyclic3
  · exact q066_cyclic4
  · exact q066_cyclic5
  · exact q066_cyclic6
  · exact q066_cyclic7
  · exact q066_cyclic8
  · exact q066_cyclic9
  · exact q066_cyclic10
  · exact q066_cyclic11
  · exact q066_cyclic12
  · exact q066_cyclic13
  · exact q066_cyclic14
  · exact q066_cyclic15
  · exact q066_cyclic16
  · exact q066_cyclic17
  · exact q066_cyclic18
  · exact q066_cyclic19
  · exact q066_cyclic20
  · exact q066_cyclic21
  · exact q066_cyclic22
  · exact q066_cyclic23
  · exact q066_cyclic24
  · exact q066_cyclic25

theorem q066_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q066.node i) = true := by
  intro i
  change Fin 26 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q066_triangles0
  · exact q066_triangles1
  · exact q066_triangles2
  · exact q066_triangles3
  · exact q066_triangles4
  · exact q066_triangles5
  · exact q066_triangles6
  · exact q066_triangles7
  · exact q066_triangles8
  · exact q066_triangles9
  · exact q066_triangles10
  · exact q066_triangles11
  · exact q066_triangles12
  · exact q066_triangles13
  · exact q066_triangles14
  · exact q066_triangles15
  · exact q066_triangles16
  · exact q066_triangles17
  · exact q066_triangles18
  · exact q066_triangles19
  · exact q066_triangles20
  · exact q066_triangles21
  · exact q066_triangles22
  · exact q066_triangles23
  · exact q066_triangles24
  · exact q066_triangles25

theorem q066_descents : ∀ i, allTriangleDescentsCheck (BoundedLStarData.q066.node i) = true := by
  intro i
  change Fin 26 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q066_descent0
  · exact q066_descent1
  · exact q066_descent2
  · exact q066_descent3
  · exact q066_descent4
  · exact q066_descent5
  · exact q066_descent6
  · exact q066_descent7
  · exact q066_descent8
  · exact q066_descent9
  · exact q066_descent10
  · exact q066_descent11
  · exact q066_descent12
  · exact q066_descent13
  · exact q066_descent14
  · exact q066_descent15
  · exact q066_descent16
  · exact q066_descent17
  · exact q066_descent18
  · exact q066_descent19
  · exact q066_descent20
  · exact q066_descent21
  · exact q066_descent22
  · exact q066_descent23
  · exact q066_descent24
  · exact q066_descent25

theorem q066_edges : ∀ i k, EdgeChecks BoundedLStarData.q066 i k ((BoundedLStarData.q066.core i).edges k) := by
  intro i k
  change Fin 26 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge0_0
    · exact q066_edge0_1
    · exact q066_edge0_2
    · exact q066_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge1_0
    · exact q066_edge1_1
    · exact q066_edge1_2
    · exact q066_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge2_0
    · exact q066_edge2_1
    · exact q066_edge2_2
    · exact q066_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge3_0
    · exact q066_edge3_1
    · exact q066_edge3_2
    · exact q066_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge4_0
    · exact q066_edge4_1
    · exact q066_edge4_2
    · exact q066_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge5_0
    · exact q066_edge5_1
    · exact q066_edge5_2
    · exact q066_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge6_0
    · exact q066_edge6_1
    · exact q066_edge6_2
    · exact q066_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge7_0
    · exact q066_edge7_1
    · exact q066_edge7_2
    · exact q066_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge8_0
    · exact q066_edge8_1
    · exact q066_edge8_2
    · exact q066_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge9_0
    · exact q066_edge9_1
    · exact q066_edge9_2
    · exact q066_edge9_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge10_0
    · exact q066_edge10_1
    · exact q066_edge10_2
    · exact q066_edge10_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge11_0
    · exact q066_edge11_1
    · exact q066_edge11_2
    · exact q066_edge11_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge12_0
    · exact q066_edge12_1
    · exact q066_edge12_2
    · exact q066_edge12_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge13_0
    · exact q066_edge13_1
    · exact q066_edge13_2
    · exact q066_edge13_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge14_0
    · exact q066_edge14_1
    · exact q066_edge14_2
    · exact q066_edge14_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge15_0
    · exact q066_edge15_1
    · exact q066_edge15_2
    · exact q066_edge15_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge16_0
    · exact q066_edge16_1
    · exact q066_edge16_2
    · exact q066_edge16_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge17_0
    · exact q066_edge17_1
    · exact q066_edge17_2
    · exact q066_edge17_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge18_0
    · exact q066_edge18_1
    · exact q066_edge18_2
    · exact q066_edge18_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge19_0
    · exact q066_edge19_1
    · exact q066_edge19_2
    · exact q066_edge19_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge20_0
    · exact q066_edge20_1
    · exact q066_edge20_2
    · exact q066_edge20_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge21_0
    · exact q066_edge21_1
    · exact q066_edge21_2
    · exact q066_edge21_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge22_0
    · exact q066_edge22_1
    · exact q066_edge22_2
    · exact q066_edge22_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge23_0
    · exact q066_edge23_1
    · exact q066_edge23_2
    · exact q066_edge23_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge24_0
    · exact q066_edge24_1
    · exact q066_edge24_2
    · exact q066_edge24_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q066_edge25_0
    · exact q066_edge25_1
    · exact q066_edge25_2
    · exact q066_edge25_3

theorem q066_checks : Checks BoundedLStarData.q066 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := q066_reachable
  cyclic := q066_cyclic
  strips := by
    intro s
    change Fin 2 at s
    have h : s=0 ∨ s=1 := by omega
    rcases h with rfl|rfl
    · exact q066_strip0
    · exact q066_strip1
  edges := q066_edges
  triangles := (decide_eq_true q066_triangles).symm
  descents := fun _ => q066_descents

end QuiverProofs.BoundedLStarChecks
