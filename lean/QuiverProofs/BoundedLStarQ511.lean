import QuiverProofs.BoundedLStarData
import QuiverProofs.LStarCertificate
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem q511_prefix0 : applyWord (BoundedLStarData.q511.node 0) [] = (ofSix (-2) (-1) (2) (-1) (0) (-2)) := by
  rfl

private theorem q511_prefix1 : applyWord (BoundedLStarData.q511.node 0) [0] = (ofSix (2) (1) (-2) (-1) (4) (0)) := by
  rw [show ([0] : List (Fin 4)) = [] ++ [0] from rfl,
    applyWord_append,q511_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix2 : applyWord (BoundedLStarData.q511.node 0) [1] = (ofSix (2) (-3) (2) (1) (0) (-2)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,q511_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix3 : applyWord (BoundedLStarData.q511.node 0) [0,1] = (ofSix (-2) (1) (6) (1) (-4) (4)) := by
  rw [show ([0,1] : List (Fin 4)) = [0] ++ [1] from rfl,
    applyWord_append,q511_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix4 : applyWord (BoundedLStarData.q511.node 0) [0,2] = (ofSix (3) (-1) (-2) (1) (4) (0)) := by
  rw [show ([0,2] : List (Fin 4)) = [0] ++ [2] from rfl,
    applyWord_append,q511_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix5 : applyWord (BoundedLStarData.q511.node 0) [0,3] = (ofSix (-6) (1) (2) (-1) (-4) (0)) := by
  rw [show ([0,3] : List (Fin 4)) = [0] ++ [3] from rfl,
    applyWord_append,q511_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix6 : applyWord (BoundedLStarData.q511.node 0) [0,1,0] = (ofSix (2) (-1) (-6) (3) (8) (4)) := by
  rw [show ([0,1,0] : List (Fin 4)) = [0,1] ++ [0] from rfl,
    applyWord_append,q511_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix7 : applyWord (BoundedLStarData.q511.node 0) [0,1,2] = (ofSix (-2) (-1) (10) (-1) (0) (-4)) := by
  rw [show ([0,1,2] : List (Fin 4)) = [0,1] ++ [2] from rfl,
    applyWord_append,q511_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix8 : applyWord (BoundedLStarData.q511.node 0) [0,2,1] = (ofSix (-3) (2) (10) (-1) (-4) (0)) := by
  rw [show ([0,2,1] : List (Fin 4)) = [0,2] ++ [1] from rfl,
    applyWord_append,q511_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix9 : applyWord (BoundedLStarData.q511.node 0) [0,2,3] = (ofSix (-5) (-1) (2) (1) (-4) (0)) := by
  rw [show ([0,2,3] : List (Fin 4)) = [0,2] ++ [3] from rfl,
    applyWord_append,q511_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix10 : applyWord (BoundedLStarData.q511.node 0) [0,3,0] = (ofSix (6) (-1) (-2) (5) (8) (0)) := by
  rw [show ([0,3,0] : List (Fin 4)) = [0,3] ++ [0] from rfl,
    applyWord_append,q511_prefix5]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix11 : applyWord (BoundedLStarData.q511.node 0) [0,3,1] = (ofSix (6) (-5) (-22) (1) (4) (0)) := by
  rw [show ([0,3,1] : List (Fin 4)) = [0,3] ++ [1] from rfl,
    applyWord_append,q511_prefix5]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix12 : applyWord (BoundedLStarData.q511.node 0) [0,1,0,2] = (ofSix (-1) (1) (-6) (-3) (20) (-4)) := by
  rw [show ([0,1,0,2] : List (Fin 4)) = [0,1,0] ++ [2] from rfl,
    applyWord_append,q511_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix13 : applyWord (BoundedLStarData.q511.node 0) [0,1,2,0] = (ofSix (2) (1) (-10) (-1) (20) (6)) := by
  rw [show ([0,1,2,0] : List (Fin 4)) = [0,1,2] ++ [0] from rfl,
    applyWord_append,q511_prefix7]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix14 : applyWord (BoundedLStarData.q511.node 0) [0,2,3,0] = (ofSix (5) (1) (-2) (1) (6) (2)) := by
  rw [show ([0,2,3,0] : List (Fin 4)) = [0,2,3] ++ [0] from rfl,
    applyWord_append,q511_prefix9]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix15 : applyWord (BoundedLStarData.q511.node 0) [0,2,3,1] = (ofSix (5) (-1) (-18) (-1) (4) (-4)) := by
  rw [show ([0,2,3,1] : List (Fin 4)) = [0,2,3] ++ [1] from rfl,
    applyWord_append,q511_prefix9]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix16 : applyWord (BoundedLStarData.q511.node 0) [0,3,0,2] = (ofSix (1) (1) (-2) (-5) (8) (0)) := by
  rw [show ([0,3,0,2] : List (Fin 4)) = [0,3,0] ++ [2] from rfl,
    applyWord_append,q511_prefix10]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix17 : applyWord (BoundedLStarData.q511.node 0) [0,3,1,2] = (ofSix (1) (5) (-22) (-1) (4) (0)) := by
  rw [show ([0,3,1,2] : List (Fin 4)) = [0,3,1] ++ [2] from rfl,
    applyWord_append,q511_prefix11]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix18 : applyWord (BoundedLStarData.q511.node 0) [0,1,0,2,1] = (ofSix (1) (-2) (-6) (3) (-20) (56)) := by
  rw [show ([0,1,0,2,1] : List (Fin 4)) = [0,1,0,2] ++ [1] from rfl,
    applyWord_append,q511_prefix12]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix19 : applyWord (BoundedLStarData.q511.node 0) [0,2,3,0,1] = (ofSix (-5) (6) (28) (-1) (-6) (2)) := by
  rw [show ([0,2,3,0,1] : List (Fin 4)) = [0,2,3,0] ++ [1] from rfl,
    applyWord_append,q511_prefix14]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix20 : applyWord (BoundedLStarData.q511.node 0) [0,2,3,1,0] = (ofSix (-5) (1) (18) (-6) (-86) (-4)) := by
  rw [show ([0,2,3,1,0] : List (Fin 4)) = [0,2,3,1] ++ [0] from rfl,
    applyWord_append,q511_prefix15]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix21 : applyWord (BoundedLStarData.q511.node 0) [0,3,0,2,1] = (ofSix (-1) (1) (6) (5) (-8) (40)) := by
  rw [show ([0,3,0,2,1] : List (Fin 4)) = [0,3,0,2] ++ [1] from rfl,
    applyWord_append,q511_prefix16]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix22 : applyWord (BoundedLStarData.q511.node 0) [0,3,1,2,0] = (ofSix (-1) (-5) (22) (-1) (-18) (-110)) := by
  rw [show ([0,3,1,2,0] : List (Fin 4)) = [0,3,1,2] ++ [0] from rfl,
    applyWord_append,q511_prefix17]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix23 : applyWord (BoundedLStarData.q511.node 0) [0,2,3,0,1,2] = (ofSix (1) (-6) (40) (1) (-6) (-2)) := by
  rw [show ([0,2,3,0,1,2] : List (Fin 4)) = [0,2,3,0,1] ++ [2] from rfl,
    applyWord_append,q511_prefix19]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix24 : applyWord (BoundedLStarData.q511.node 0) [0,2,3,1,0,2] = (ofSix (1) (-1) (18) (6) (-110) (4)) := by
  rw [show ([0,2,3,1,0,2] : List (Fin 4)) = [0,2,3,1,0] ++ [2] from rfl,
    applyWord_append,q511_prefix20]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix25 : applyWord (BoundedLStarData.q511.node 0) [0,3,0,2,1,2] = (ofSix (-1) (-1) (46) (-5) (192) (-40)) := by
  rw [show ([0,3,0,2,1,2] : List (Fin 4)) = [0,3,0,2,1] ++ [2] from rfl,
    applyWord_append,q511_prefix21]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix26 : applyWord (BoundedLStarData.q511.node 0) [0,3,1,2,0,2] = (ofSix (-1) (5) (-528) (1) (-128) (110)) := by
  rw [show ([0,3,1,2,0,2] : List (Fin 4)) = [0,3,1,2,0] ++ [2] from rfl,
    applyWord_append,q511_prefix22]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix27 : applyWord (BoundedLStarData.q511.node 0) [0,3,0,2,1,2,0] = (ofSix (1) (1) (-46) (-5) (238) (6)) := by
  rw [show ([0,3,0,2,1,2,0] : List (Fin 4)) = [0,3,0,2,1,2] ++ [0] from rfl,
    applyWord_append,q511_prefix25]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix28 : applyWord (BoundedLStarData.q511.node 0) [0,3,1,2,0,2,1] = (ofSix (1) (5) (-656) (-1) (128) (-18)) := by
  rw [show ([0,3,1,2,0,2,1] : List (Fin 4)) = [0,3,1,2,0,2] ++ [1] from rfl,
    applyWord_append,q511_prefix26]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix29 : applyWord (BoundedLStarData.q511.node 0) [0,3,0,2,1,2,0,2] = (ofSix (6) (-1) (-40) (5) (238) (-6)) := by
  rw [show ([0,3,0,2,1,2,0,2] : List (Fin 4)) = [0,3,0,2,1,2,0] ++ [2] from rfl,
    applyWord_append,q511_prefix27]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_prefix30 : applyWord (BoundedLStarData.q511.node 0) [0,3,1,2,0,2,1,2] = (ofSix (6) (-5) (-656) (1) (110) (18)) := by
  rw [show ([0,3,1,2,0,2,1,2] : List (Fin 4)) = [0,3,1,2,0,2,1] ++ [2] from rfl,
    applyWord_append,q511_prefix28]
  apply entriesEqual_eq
  decide +kernel

private theorem q511_reachable0 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 0).word) (BoundedLStarData.q511.node 0) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) []) (ofSix (-2) (-1) (2) (-1) (0) (-2))
  rw [q511_prefix0]
  intro u v; rfl

private theorem q511_cyclic0 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 0) := by decide +kernel

private theorem q511_edge0_0 :
    EdgeChecks BoundedLStarData.q511 0 0 ((BoundedLStarData.q511.core 0).edges 0) := by decide +kernel

private theorem q511_edge0_1 :
    EdgeChecks BoundedLStarData.q511 0 1 ((BoundedLStarData.q511.core 0).edges 1) := by decide +kernel

private theorem q511_edge0_2 :
    EdgeChecks BoundedLStarData.q511 0 2 ((BoundedLStarData.q511.core 0).edges 2) := by decide +kernel

private theorem q511_edge0_3 :
    EdgeChecks BoundedLStarData.q511 0 3 ((BoundedLStarData.q511.core 0).edges 3) := by decide +kernel

private theorem q511_triangles0 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 0) = true := by decide +kernel

private theorem q511_descent0 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-1) (2) (-1) (0) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable1 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 1).word) (BoundedLStarData.q511.node 1) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0]) (ofSix (2) (1) (-2) (-1) (4) (0))
  rw [q511_prefix1]
  intro u v; rfl

private theorem q511_cyclic1 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 1) := by decide +kernel

private theorem q511_edge1_0 :
    EdgeChecks BoundedLStarData.q511 1 0 ((BoundedLStarData.q511.core 1).edges 0) := by decide +kernel

private theorem q511_edge1_1 :
    EdgeChecks BoundedLStarData.q511 1 1 ((BoundedLStarData.q511.core 1).edges 1) := by decide +kernel

private theorem q511_edge1_2 :
    EdgeChecks BoundedLStarData.q511 1 2 ((BoundedLStarData.q511.core 1).edges 2) := by decide +kernel

private theorem q511_edge1_3 :
    EdgeChecks BoundedLStarData.q511 1 3 ((BoundedLStarData.q511.core 1).edges 3) := by decide +kernel

private theorem q511_triangles1 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 1) = true := by decide +kernel

private theorem q511_descent1 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (1) (-2) (-1) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable2 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 2).word) (BoundedLStarData.q511.node 2) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [1]) (ofSix (2) (-3) (2) (1) (0) (-2))
  rw [q511_prefix2]
  intro u v; rfl

private theorem q511_cyclic2 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 2) := by decide +kernel

private theorem q511_edge2_0 :
    EdgeChecks BoundedLStarData.q511 2 0 ((BoundedLStarData.q511.core 2).edges 0) := by decide +kernel

private theorem q511_edge2_1 :
    EdgeChecks BoundedLStarData.q511 2 1 ((BoundedLStarData.q511.core 2).edges 1) := by decide +kernel

private theorem q511_edge2_2 :
    EdgeChecks BoundedLStarData.q511 2 2 ((BoundedLStarData.q511.core 2).edges 2) := by decide +kernel

private theorem q511_edge2_3 :
    EdgeChecks BoundedLStarData.q511 2 3 ((BoundedLStarData.q511.core 2).edges 3) := by decide +kernel

private theorem q511_triangles2 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 2) = true := by decide +kernel

private theorem q511_descent2 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-3) (2) (1) (0) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable3 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 3).word) (BoundedLStarData.q511.node 3) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,1]) (ofSix (-2) (1) (6) (1) (-4) (4))
  rw [q511_prefix3]
  intro u v; rfl

private theorem q511_cyclic3 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 3) := by decide +kernel

private theorem q511_edge3_0 :
    EdgeChecks BoundedLStarData.q511 3 0 ((BoundedLStarData.q511.core 3).edges 0) := by decide +kernel

private theorem q511_edge3_1 :
    EdgeChecks BoundedLStarData.q511 3 1 ((BoundedLStarData.q511.core 3).edges 1) := by decide +kernel

private theorem q511_edge3_2 :
    EdgeChecks BoundedLStarData.q511 3 2 ((BoundedLStarData.q511.core 3).edges 2) := by decide +kernel

private theorem q511_edge3_3 :
    EdgeChecks BoundedLStarData.q511 3 3 ((BoundedLStarData.q511.core 3).edges 3) := by decide +kernel

private theorem q511_triangles3 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 3) = true := by decide +kernel

private theorem q511_descent3 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (1) (6) (1) (-4) (4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable4 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 4).word) (BoundedLStarData.q511.node 4) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2]) (ofSix (3) (-1) (-2) (1) (4) (0))
  rw [q511_prefix4]
  intro u v; rfl

private theorem q511_cyclic4 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 4) := by decide +kernel

private theorem q511_edge4_0 :
    EdgeChecks BoundedLStarData.q511 4 0 ((BoundedLStarData.q511.core 4).edges 0) := by decide +kernel

private theorem q511_edge4_1 :
    EdgeChecks BoundedLStarData.q511 4 1 ((BoundedLStarData.q511.core 4).edges 1) := by decide +kernel

private theorem q511_edge4_2 :
    EdgeChecks BoundedLStarData.q511 4 2 ((BoundedLStarData.q511.core 4).edges 2) := by decide +kernel

private theorem q511_edge4_3 :
    EdgeChecks BoundedLStarData.q511 4 3 ((BoundedLStarData.q511.core 4).edges 3) := by decide +kernel

private theorem q511_triangles4 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 4) = true := by decide +kernel

private theorem q511_descent4 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (3) (-1) (-2) (1) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable5 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 5).word) (BoundedLStarData.q511.node 5) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3]) (ofSix (-6) (1) (2) (-1) (-4) (0))
  rw [q511_prefix5]
  intro u v; rfl

private theorem q511_cyclic5 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 5) := by decide +kernel

private theorem q511_edge5_0 :
    EdgeChecks BoundedLStarData.q511 5 0 ((BoundedLStarData.q511.core 5).edges 0) := by decide +kernel

private theorem q511_edge5_1 :
    EdgeChecks BoundedLStarData.q511 5 1 ((BoundedLStarData.q511.core 5).edges 1) := by decide +kernel

private theorem q511_edge5_2 :
    EdgeChecks BoundedLStarData.q511 5 2 ((BoundedLStarData.q511.core 5).edges 2) := by decide +kernel

private theorem q511_edge5_3 :
    EdgeChecks BoundedLStarData.q511 5 3 ((BoundedLStarData.q511.core 5).edges 3) := by decide +kernel

private theorem q511_triangles5 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 5) = true := by decide +kernel

private theorem q511_descent5 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (1) (2) (-1) (-4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable6 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 6).word) (BoundedLStarData.q511.node 6) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,1,0]) (ofSix (2) (-1) (-6) (3) (8) (4))
  rw [q511_prefix6]
  intro u v; rfl

private theorem q511_cyclic6 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 6) := by decide +kernel

private theorem q511_edge6_0 :
    EdgeChecks BoundedLStarData.q511 6 0 ((BoundedLStarData.q511.core 6).edges 0) := by decide +kernel

private theorem q511_edge6_1 :
    EdgeChecks BoundedLStarData.q511 6 1 ((BoundedLStarData.q511.core 6).edges 1) := by decide +kernel

private theorem q511_edge6_2 :
    EdgeChecks BoundedLStarData.q511 6 2 ((BoundedLStarData.q511.core 6).edges 2) := by decide +kernel

private theorem q511_edge6_3 :
    EdgeChecks BoundedLStarData.q511 6 3 ((BoundedLStarData.q511.core 6).edges 3) := by decide +kernel

private theorem q511_triangles6 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 6) = true := by decide +kernel

private theorem q511_descent6 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (-6) (3) (8) (4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable7 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 7).word) (BoundedLStarData.q511.node 7) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,1,2]) (ofSix (-2) (-1) (10) (-1) (0) (-4))
  rw [q511_prefix7]
  intro u v; rfl

private theorem q511_cyclic7 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 7) := by decide +kernel

private theorem q511_edge7_0 :
    EdgeChecks BoundedLStarData.q511 7 0 ((BoundedLStarData.q511.core 7).edges 0) := by decide +kernel

private theorem q511_edge7_1 :
    EdgeChecks BoundedLStarData.q511 7 1 ((BoundedLStarData.q511.core 7).edges 1) := by decide +kernel

private theorem q511_edge7_2 :
    EdgeChecks BoundedLStarData.q511 7 2 ((BoundedLStarData.q511.core 7).edges 2) := by decide +kernel

private theorem q511_edge7_3 :
    EdgeChecks BoundedLStarData.q511 7 3 ((BoundedLStarData.q511.core 7).edges 3) := by decide +kernel

private theorem q511_triangles7 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 7) = true := by decide +kernel

private theorem q511_descent7 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-1) (10) (-1) (0) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable8 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 8).word) (BoundedLStarData.q511.node 8) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,1]) (ofSix (-3) (2) (10) (-1) (-4) (0))
  rw [q511_prefix8]
  intro u v; rfl

private theorem q511_cyclic8 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 8) := by decide +kernel

private theorem q511_edge8_0 :
    EdgeChecks BoundedLStarData.q511 8 0 ((BoundedLStarData.q511.core 8).edges 0) := by decide +kernel

private theorem q511_edge8_1 :
    EdgeChecks BoundedLStarData.q511 8 1 ((BoundedLStarData.q511.core 8).edges 1) := by decide +kernel

private theorem q511_edge8_2 :
    EdgeChecks BoundedLStarData.q511 8 2 ((BoundedLStarData.q511.core 8).edges 2) := by decide +kernel

private theorem q511_edge8_3 :
    EdgeChecks BoundedLStarData.q511 8 3 ((BoundedLStarData.q511.core 8).edges 3) := by decide +kernel

private theorem q511_triangles8 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 8) = true := by decide +kernel

private theorem q511_descent8 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (-3) (2) (10) (-1) (-4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable9 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 9).word) (BoundedLStarData.q511.node 9) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,3]) (ofSix (-5) (-1) (2) (1) (-4) (0))
  rw [q511_prefix9]
  intro u v; rfl

private theorem q511_cyclic9 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 9) := by decide +kernel

private theorem q511_edge9_0 :
    EdgeChecks BoundedLStarData.q511 9 0 ((BoundedLStarData.q511.core 9).edges 0) := by decide +kernel

private theorem q511_edge9_1 :
    EdgeChecks BoundedLStarData.q511 9 1 ((BoundedLStarData.q511.core 9).edges 1) := by decide +kernel

private theorem q511_edge9_2 :
    EdgeChecks BoundedLStarData.q511 9 2 ((BoundedLStarData.q511.core 9).edges 2) := by decide +kernel

private theorem q511_edge9_3 :
    EdgeChecks BoundedLStarData.q511 9 3 ((BoundedLStarData.q511.core 9).edges 3) := by decide +kernel

private theorem q511_triangles9 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 9) = true := by decide +kernel

private theorem q511_descent9 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (-5) (-1) (2) (1) (-4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable10 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 10).word) (BoundedLStarData.q511.node 10) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,0]) (ofSix (6) (-1) (-2) (5) (8) (0))
  rw [q511_prefix10]
  intro u v; rfl

private theorem q511_cyclic10 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 10) := by decide +kernel

private theorem q511_edge10_0 :
    EdgeChecks BoundedLStarData.q511 10 0 ((BoundedLStarData.q511.core 10).edges 0) := by decide +kernel

private theorem q511_edge10_1 :
    EdgeChecks BoundedLStarData.q511 10 1 ((BoundedLStarData.q511.core 10).edges 1) := by decide +kernel

private theorem q511_edge10_2 :
    EdgeChecks BoundedLStarData.q511 10 2 ((BoundedLStarData.q511.core 10).edges 2) := by decide +kernel

private theorem q511_edge10_3 :
    EdgeChecks BoundedLStarData.q511 10 3 ((BoundedLStarData.q511.core 10).edges 3) := by decide +kernel

private theorem q511_triangles10 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 10) = true := by decide +kernel

private theorem q511_descent10 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 10) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-1) (-2) (5) (8) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable11 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 11).word) (BoundedLStarData.q511.node 11) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,1]) (ofSix (6) (-5) (-22) (1) (4) (0))
  rw [q511_prefix11]
  intro u v; rfl

private theorem q511_cyclic11 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 11) := by decide +kernel

private theorem q511_edge11_0 :
    EdgeChecks BoundedLStarData.q511 11 0 ((BoundedLStarData.q511.core 11).edges 0) := by decide +kernel

private theorem q511_edge11_1 :
    EdgeChecks BoundedLStarData.q511 11 1 ((BoundedLStarData.q511.core 11).edges 1) := by decide +kernel

private theorem q511_edge11_2 :
    EdgeChecks BoundedLStarData.q511 11 2 ((BoundedLStarData.q511.core 11).edges 2) := by decide +kernel

private theorem q511_edge11_3 :
    EdgeChecks BoundedLStarData.q511 11 3 ((BoundedLStarData.q511.core 11).edges 3) := by decide +kernel

private theorem q511_triangles11 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 11) = true := by decide +kernel

private theorem q511_descent11 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 11) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-5) (-22) (1) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable12 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 12).word) (BoundedLStarData.q511.node 12) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,1,0,2]) (ofSix (-1) (1) (-6) (-3) (20) (-4))
  rw [q511_prefix12]
  intro u v; rfl

private theorem q511_cyclic12 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 12) := by decide +kernel

private theorem q511_edge12_0 :
    EdgeChecks BoundedLStarData.q511 12 0 ((BoundedLStarData.q511.core 12).edges 0) := by decide +kernel

private theorem q511_edge12_1 :
    EdgeChecks BoundedLStarData.q511 12 1 ((BoundedLStarData.q511.core 12).edges 1) := by decide +kernel

private theorem q511_edge12_2 :
    EdgeChecks BoundedLStarData.q511 12 2 ((BoundedLStarData.q511.core 12).edges 2) := by decide +kernel

private theorem q511_edge12_3 :
    EdgeChecks BoundedLStarData.q511 12 3 ((BoundedLStarData.q511.core 12).edges 3) := by decide +kernel

private theorem q511_triangles12 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 12) = true := by decide +kernel

private theorem q511_descent12 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 12) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (1) (-6) (-3) (20) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable13 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 13).word) (BoundedLStarData.q511.node 13) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,1,2,0]) (ofSix (2) (1) (-10) (-1) (20) (6))
  rw [q511_prefix13]
  intro u v; rfl

private theorem q511_cyclic13 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 13) := by decide +kernel

private theorem q511_edge13_0 :
    EdgeChecks BoundedLStarData.q511 13 0 ((BoundedLStarData.q511.core 13).edges 0) := by decide +kernel

private theorem q511_edge13_1 :
    EdgeChecks BoundedLStarData.q511 13 1 ((BoundedLStarData.q511.core 13).edges 1) := by decide +kernel

private theorem q511_edge13_2 :
    EdgeChecks BoundedLStarData.q511 13 2 ((BoundedLStarData.q511.core 13).edges 2) := by decide +kernel

private theorem q511_edge13_3 :
    EdgeChecks BoundedLStarData.q511 13 3 ((BoundedLStarData.q511.core 13).edges 3) := by decide +kernel

private theorem q511_triangles13 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 13) = true := by decide +kernel

private theorem q511_descent13 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 13) = true := by
  change allTriangleDescentsCheck (ofSix (2) (1) (-10) (-1) (20) (6)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable14 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 14).word) (BoundedLStarData.q511.node 14) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,3,0]) (ofSix (5) (1) (-2) (1) (6) (2))
  rw [q511_prefix14]
  intro u v; rfl

private theorem q511_cyclic14 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 14) := by decide +kernel

private theorem q511_edge14_0 :
    EdgeChecks BoundedLStarData.q511 14 0 ((BoundedLStarData.q511.core 14).edges 0) := by decide +kernel

private theorem q511_edge14_1 :
    EdgeChecks BoundedLStarData.q511 14 1 ((BoundedLStarData.q511.core 14).edges 1) := by decide +kernel

private theorem q511_edge14_2 :
    EdgeChecks BoundedLStarData.q511 14 2 ((BoundedLStarData.q511.core 14).edges 2) := by decide +kernel

private theorem q511_edge14_3 :
    EdgeChecks BoundedLStarData.q511 14 3 ((BoundedLStarData.q511.core 14).edges 3) := by decide +kernel

private theorem q511_triangles14 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 14) = true := by decide +kernel

private theorem q511_descent14 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 14) = true := by
  change allTriangleDescentsCheck (ofSix (5) (1) (-2) (1) (6) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable15 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 15).word) (BoundedLStarData.q511.node 15) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,3,1]) (ofSix (5) (-1) (-18) (-1) (4) (-4))
  rw [q511_prefix15]
  intro u v; rfl

private theorem q511_cyclic15 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 15) := by decide +kernel

private theorem q511_edge15_0 :
    EdgeChecks BoundedLStarData.q511 15 0 ((BoundedLStarData.q511.core 15).edges 0) := by decide +kernel

private theorem q511_edge15_1 :
    EdgeChecks BoundedLStarData.q511 15 1 ((BoundedLStarData.q511.core 15).edges 1) := by decide +kernel

private theorem q511_edge15_2 :
    EdgeChecks BoundedLStarData.q511 15 2 ((BoundedLStarData.q511.core 15).edges 2) := by decide +kernel

private theorem q511_edge15_3 :
    EdgeChecks BoundedLStarData.q511 15 3 ((BoundedLStarData.q511.core 15).edges 3) := by decide +kernel

private theorem q511_triangles15 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 15) = true := by decide +kernel

private theorem q511_descent15 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 15) = true := by
  change allTriangleDescentsCheck (ofSix (5) (-1) (-18) (-1) (4) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable16 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 16).word) (BoundedLStarData.q511.node 16) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,0,2]) (ofSix (1) (1) (-2) (-5) (8) (0))
  rw [q511_prefix16]
  intro u v; rfl

private theorem q511_cyclic16 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 16) := by decide +kernel

private theorem q511_edge16_0 :
    EdgeChecks BoundedLStarData.q511 16 0 ((BoundedLStarData.q511.core 16).edges 0) := by decide +kernel

private theorem q511_edge16_1 :
    EdgeChecks BoundedLStarData.q511 16 1 ((BoundedLStarData.q511.core 16).edges 1) := by decide +kernel

private theorem q511_edge16_2 :
    EdgeChecks BoundedLStarData.q511 16 2 ((BoundedLStarData.q511.core 16).edges 2) := by decide +kernel

private theorem q511_edge16_3 :
    EdgeChecks BoundedLStarData.q511 16 3 ((BoundedLStarData.q511.core 16).edges 3) := by decide +kernel

private theorem q511_triangles16 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 16) = true := by decide +kernel

private theorem q511_descent16 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 16) = true := by
  change allTriangleDescentsCheck (ofSix (1) (1) (-2) (-5) (8) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable17 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 17).word) (BoundedLStarData.q511.node 17) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,1,2]) (ofSix (1) (5) (-22) (-1) (4) (0))
  rw [q511_prefix17]
  intro u v; rfl

private theorem q511_cyclic17 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 17) := by decide +kernel

private theorem q511_edge17_0 :
    EdgeChecks BoundedLStarData.q511 17 0 ((BoundedLStarData.q511.core 17).edges 0) := by decide +kernel

private theorem q511_edge17_1 :
    EdgeChecks BoundedLStarData.q511 17 1 ((BoundedLStarData.q511.core 17).edges 1) := by decide +kernel

private theorem q511_edge17_2 :
    EdgeChecks BoundedLStarData.q511 17 2 ((BoundedLStarData.q511.core 17).edges 2) := by decide +kernel

private theorem q511_edge17_3 :
    EdgeChecks BoundedLStarData.q511 17 3 ((BoundedLStarData.q511.core 17).edges 3) := by decide +kernel

private theorem q511_triangles17 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 17) = true := by decide +kernel

private theorem q511_descent17 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 17) = true := by
  change allTriangleDescentsCheck (ofSix (1) (5) (-22) (-1) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable18 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 18).word) (BoundedLStarData.q511.node 18) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,1,0,2,1]) (ofSix (1) (-2) (-6) (3) (-20) (56))
  rw [q511_prefix18]
  intro u v; rfl

private theorem q511_cyclic18 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 18) := by decide +kernel

private theorem q511_edge18_0 :
    EdgeChecks BoundedLStarData.q511 18 0 ((BoundedLStarData.q511.core 18).edges 0) := by decide +kernel

private theorem q511_edge18_1 :
    EdgeChecks BoundedLStarData.q511 18 1 ((BoundedLStarData.q511.core 18).edges 1) := by decide +kernel

private theorem q511_edge18_2 :
    EdgeChecks BoundedLStarData.q511 18 2 ((BoundedLStarData.q511.core 18).edges 2) := by decide +kernel

private theorem q511_edge18_3 :
    EdgeChecks BoundedLStarData.q511 18 3 ((BoundedLStarData.q511.core 18).edges 3) := by decide +kernel

private theorem q511_triangles18 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 18) = true := by decide +kernel

private theorem q511_descent18 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 18) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-2) (-6) (3) (-20) (56)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable19 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 19).word) (BoundedLStarData.q511.node 19) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,3,0,1]) (ofSix (-5) (6) (28) (-1) (-6) (2))
  rw [q511_prefix19]
  intro u v; rfl

private theorem q511_cyclic19 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 19) := by decide +kernel

private theorem q511_edge19_0 :
    EdgeChecks BoundedLStarData.q511 19 0 ((BoundedLStarData.q511.core 19).edges 0) := by decide +kernel

private theorem q511_edge19_1 :
    EdgeChecks BoundedLStarData.q511 19 1 ((BoundedLStarData.q511.core 19).edges 1) := by decide +kernel

private theorem q511_edge19_2 :
    EdgeChecks BoundedLStarData.q511 19 2 ((BoundedLStarData.q511.core 19).edges 2) := by decide +kernel

private theorem q511_edge19_3 :
    EdgeChecks BoundedLStarData.q511 19 3 ((BoundedLStarData.q511.core 19).edges 3) := by decide +kernel

private theorem q511_triangles19 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 19) = true := by decide +kernel

private theorem q511_descent19 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 19) = true := by
  change allTriangleDescentsCheck (ofSix (-5) (6) (28) (-1) (-6) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable20 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 20).word) (BoundedLStarData.q511.node 20) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,3,1,0]) (ofSix (-5) (1) (18) (-6) (-86) (-4))
  rw [q511_prefix20]
  intro u v; rfl

private theorem q511_cyclic20 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 20) := by decide +kernel

private theorem q511_edge20_0 :
    EdgeChecks BoundedLStarData.q511 20 0 ((BoundedLStarData.q511.core 20).edges 0) := by decide +kernel

private theorem q511_edge20_1 :
    EdgeChecks BoundedLStarData.q511 20 1 ((BoundedLStarData.q511.core 20).edges 1) := by decide +kernel

private theorem q511_edge20_2 :
    EdgeChecks BoundedLStarData.q511 20 2 ((BoundedLStarData.q511.core 20).edges 2) := by decide +kernel

private theorem q511_edge20_3 :
    EdgeChecks BoundedLStarData.q511 20 3 ((BoundedLStarData.q511.core 20).edges 3) := by decide +kernel

private theorem q511_triangles20 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 20) = true := by decide +kernel

private theorem q511_descent20 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 20) = true := by
  change allTriangleDescentsCheck (ofSix (-5) (1) (18) (-6) (-86) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable21 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 21).word) (BoundedLStarData.q511.node 21) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,0,2,1]) (ofSix (-1) (1) (6) (5) (-8) (40))
  rw [q511_prefix21]
  intro u v; rfl

private theorem q511_cyclic21 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 21) := by decide +kernel

private theorem q511_edge21_0 :
    EdgeChecks BoundedLStarData.q511 21 0 ((BoundedLStarData.q511.core 21).edges 0) := by decide +kernel

private theorem q511_edge21_1 :
    EdgeChecks BoundedLStarData.q511 21 1 ((BoundedLStarData.q511.core 21).edges 1) := by decide +kernel

private theorem q511_edge21_2 :
    EdgeChecks BoundedLStarData.q511 21 2 ((BoundedLStarData.q511.core 21).edges 2) := by decide +kernel

private theorem q511_edge21_3 :
    EdgeChecks BoundedLStarData.q511 21 3 ((BoundedLStarData.q511.core 21).edges 3) := by decide +kernel

private theorem q511_triangles21 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 21) = true := by decide +kernel

private theorem q511_descent21 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 21) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (1) (6) (5) (-8) (40)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable22 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 22).word) (BoundedLStarData.q511.node 22) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,1,2,0]) (ofSix (-1) (-5) (22) (-1) (-18) (-110))
  rw [q511_prefix22]
  intro u v; rfl

private theorem q511_cyclic22 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 22) := by decide +kernel

private theorem q511_edge22_0 :
    EdgeChecks BoundedLStarData.q511 22 0 ((BoundedLStarData.q511.core 22).edges 0) := by decide +kernel

private theorem q511_edge22_1 :
    EdgeChecks BoundedLStarData.q511 22 1 ((BoundedLStarData.q511.core 22).edges 1) := by decide +kernel

private theorem q511_edge22_2 :
    EdgeChecks BoundedLStarData.q511 22 2 ((BoundedLStarData.q511.core 22).edges 2) := by decide +kernel

private theorem q511_edge22_3 :
    EdgeChecks BoundedLStarData.q511 22 3 ((BoundedLStarData.q511.core 22).edges 3) := by decide +kernel

private theorem q511_triangles22 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 22) = true := by decide +kernel

private theorem q511_descent22 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 22) = true := by
  change allTriangleDescentsCheck (ofSix (-1) (-5) (22) (-1) (-18) (-110)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable23 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 23).word) (BoundedLStarData.q511.node 23) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,3,0,1,2]) (ofSix (1) (-6) (40) (1) (-6) (-2))
  rw [q511_prefix23]
  intro u v; rfl

private theorem q511_cyclic23 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 23) := by decide +kernel

private theorem q511_edge23_0 :
    EdgeChecks BoundedLStarData.q511 23 0 ((BoundedLStarData.q511.core 23).edges 0) := by decide +kernel

private theorem q511_edge23_1 :
    EdgeChecks BoundedLStarData.q511 23 1 ((BoundedLStarData.q511.core 23).edges 1) := by decide +kernel

private theorem q511_edge23_2 :
    EdgeChecks BoundedLStarData.q511 23 2 ((BoundedLStarData.q511.core 23).edges 2) := by decide +kernel

private theorem q511_edge23_3 :
    EdgeChecks BoundedLStarData.q511 23 3 ((BoundedLStarData.q511.core 23).edges 3) := by decide +kernel

private theorem q511_triangles23 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 23) = true := by decide +kernel

private theorem q511_descent23 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 23) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-6) (40) (1) (-6) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable24 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 24).word) (BoundedLStarData.q511.node 24) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,2,3,1,0,2]) (ofSix (1) (-1) (18) (6) (-110) (4))
  rw [q511_prefix24]
  intro u v; rfl

private theorem q511_cyclic24 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 24) := by decide +kernel

private theorem q511_edge24_0 :
    EdgeChecks BoundedLStarData.q511 24 0 ((BoundedLStarData.q511.core 24).edges 0) := by decide +kernel

private theorem q511_edge24_1 :
    EdgeChecks BoundedLStarData.q511 24 1 ((BoundedLStarData.q511.core 24).edges 1) := by decide +kernel

private theorem q511_edge24_2 :
    EdgeChecks BoundedLStarData.q511 24 2 ((BoundedLStarData.q511.core 24).edges 2) := by decide +kernel

private theorem q511_edge24_3 :
    EdgeChecks BoundedLStarData.q511 24 3 ((BoundedLStarData.q511.core 24).edges 3) := by decide +kernel

private theorem q511_triangles24 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 24) = true := by decide +kernel

private theorem q511_descent24 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 24) = true := by
  change allTriangleDescentsCheck (ofSix (1) (-1) (18) (6) (-110) (4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable25 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 25).word) (BoundedLStarData.q511.node 25) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,0,2,1,2,0,2]) (ofSix (6) (-1) (-40) (5) (238) (-6))
  rw [q511_prefix29]
  intro u v; rfl

private theorem q511_cyclic25 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 25) := by decide +kernel

private theorem q511_edge25_0 :
    EdgeChecks BoundedLStarData.q511 25 0 ((BoundedLStarData.q511.core 25).edges 0) := by decide +kernel

private theorem q511_edge25_1 :
    EdgeChecks BoundedLStarData.q511 25 1 ((BoundedLStarData.q511.core 25).edges 1) := by decide +kernel

private theorem q511_edge25_2 :
    EdgeChecks BoundedLStarData.q511 25 2 ((BoundedLStarData.q511.core 25).edges 2) := by decide +kernel

private theorem q511_edge25_3 :
    EdgeChecks BoundedLStarData.q511 25 3 ((BoundedLStarData.q511.core 25).edges 3) := by decide +kernel

private theorem q511_triangles25 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 25) = true := by decide +kernel

private theorem q511_descent25 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 25) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-1) (-40) (5) (238) (-6)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_reachable26 :
    EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core 26).word) (BoundedLStarData.q511.node 26) := by
  change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,1,2,0,2,1,2]) (ofSix (6) (-5) (-656) (1) (110) (18))
  rw [q511_prefix30]
  intro u v; rfl

private theorem q511_cyclic26 : ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node 26) := by decide +kernel

private theorem q511_edge26_0 :
    EdgeChecks BoundedLStarData.q511 26 0 ((BoundedLStarData.q511.core 26).edges 0) := by decide +kernel

private theorem q511_edge26_1 :
    EdgeChecks BoundedLStarData.q511 26 1 ((BoundedLStarData.q511.core 26).edges 1) := by decide +kernel

private theorem q511_edge26_2 :
    EdgeChecks BoundedLStarData.q511 26 2 ((BoundedLStarData.q511.core 26).edges 2) := by decide +kernel

private theorem q511_edge26_3 :
    EdgeChecks BoundedLStarData.q511 26 3 ((BoundedLStarData.q511.core 26).edges 3) := by decide +kernel

private theorem q511_triangles26 :
    TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node 26) = true := by decide +kernel

private theorem q511_descent26 :
    allTriangleDescentsCheck (BoundedLStarData.q511.node 26) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-5) (-656) (1) (110) (18)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem q511_strip0 : StripChecks BoundedLStarData.q511 (BoundedLStarData.q511.strips (0 : Fin 3)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,1,2,0]) (BoundedLStarData.q511.node 13)
    rw [q511_prefix13]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

private theorem q511_strip1 : StripChecks BoundedLStarData.q511 (BoundedLStarData.q511.strips (1 : Fin 3)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,0,2,1]) (BoundedLStarData.q511.node 21)
    rw [q511_prefix21]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

private theorem q511_strip2 : StripChecks BoundedLStarData.q511 (BoundedLStarData.q511.strips (2 : Fin 3)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (BoundedLStarData.q511.node 0) [0,3,1,2,0]) (BoundedLStarData.q511.node 22)
    rw [q511_prefix22]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

theorem q511_reachable : ∀ i, EntriesEqual (applyWord (BoundedLStarData.q511.node 0) (BoundedLStarData.q511.core i).word) (BoundedLStarData.q511.node i) := by
  intro i
  change Fin 27 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q511_reachable0
  · exact q511_reachable1
  · exact q511_reachable2
  · exact q511_reachable3
  · exact q511_reachable4
  · exact q511_reachable5
  · exact q511_reachable6
  · exact q511_reachable7
  · exact q511_reachable8
  · exact q511_reachable9
  · exact q511_reachable10
  · exact q511_reachable11
  · exact q511_reachable12
  · exact q511_reachable13
  · exact q511_reachable14
  · exact q511_reachable15
  · exact q511_reachable16
  · exact q511_reachable17
  · exact q511_reachable18
  · exact q511_reachable19
  · exact q511_reachable20
  · exact q511_reachable21
  · exact q511_reachable22
  · exact q511_reachable23
  · exact q511_reachable24
  · exact q511_reachable25
  · exact q511_reachable26

theorem q511_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (BoundedLStarData.q511.node i) := by
  intro i
  change Fin 27 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q511_cyclic0
  · exact q511_cyclic1
  · exact q511_cyclic2
  · exact q511_cyclic3
  · exact q511_cyclic4
  · exact q511_cyclic5
  · exact q511_cyclic6
  · exact q511_cyclic7
  · exact q511_cyclic8
  · exact q511_cyclic9
  · exact q511_cyclic10
  · exact q511_cyclic11
  · exact q511_cyclic12
  · exact q511_cyclic13
  · exact q511_cyclic14
  · exact q511_cyclic15
  · exact q511_cyclic16
  · exact q511_cyclic17
  · exact q511_cyclic18
  · exact q511_cyclic19
  · exact q511_cyclic20
  · exact q511_cyclic21
  · exact q511_cyclic22
  · exact q511_cyclic23
  · exact q511_cyclic24
  · exact q511_cyclic25
  · exact q511_cyclic26

theorem q511_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (BoundedLStarData.q511.node i) = true := by
  intro i
  change Fin 27 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q511_triangles0
  · exact q511_triangles1
  · exact q511_triangles2
  · exact q511_triangles3
  · exact q511_triangles4
  · exact q511_triangles5
  · exact q511_triangles6
  · exact q511_triangles7
  · exact q511_triangles8
  · exact q511_triangles9
  · exact q511_triangles10
  · exact q511_triangles11
  · exact q511_triangles12
  · exact q511_triangles13
  · exact q511_triangles14
  · exact q511_triangles15
  · exact q511_triangles16
  · exact q511_triangles17
  · exact q511_triangles18
  · exact q511_triangles19
  · exact q511_triangles20
  · exact q511_triangles21
  · exact q511_triangles22
  · exact q511_triangles23
  · exact q511_triangles24
  · exact q511_triangles25
  · exact q511_triangles26

theorem q511_descents : ∀ i, allTriangleDescentsCheck (BoundedLStarData.q511.node i) = true := by
  intro i
  change Fin 27 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact q511_descent0
  · exact q511_descent1
  · exact q511_descent2
  · exact q511_descent3
  · exact q511_descent4
  · exact q511_descent5
  · exact q511_descent6
  · exact q511_descent7
  · exact q511_descent8
  · exact q511_descent9
  · exact q511_descent10
  · exact q511_descent11
  · exact q511_descent12
  · exact q511_descent13
  · exact q511_descent14
  · exact q511_descent15
  · exact q511_descent16
  · exact q511_descent17
  · exact q511_descent18
  · exact q511_descent19
  · exact q511_descent20
  · exact q511_descent21
  · exact q511_descent22
  · exact q511_descent23
  · exact q511_descent24
  · exact q511_descent25
  · exact q511_descent26

theorem q511_edges : ∀ i k, EdgeChecks BoundedLStarData.q511 i k ((BoundedLStarData.q511.core i).edges k) := by
  intro i k
  change Fin 27 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge0_0
    · exact q511_edge0_1
    · exact q511_edge0_2
    · exact q511_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge1_0
    · exact q511_edge1_1
    · exact q511_edge1_2
    · exact q511_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge2_0
    · exact q511_edge2_1
    · exact q511_edge2_2
    · exact q511_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge3_0
    · exact q511_edge3_1
    · exact q511_edge3_2
    · exact q511_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge4_0
    · exact q511_edge4_1
    · exact q511_edge4_2
    · exact q511_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge5_0
    · exact q511_edge5_1
    · exact q511_edge5_2
    · exact q511_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge6_0
    · exact q511_edge6_1
    · exact q511_edge6_2
    · exact q511_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge7_0
    · exact q511_edge7_1
    · exact q511_edge7_2
    · exact q511_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge8_0
    · exact q511_edge8_1
    · exact q511_edge8_2
    · exact q511_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge9_0
    · exact q511_edge9_1
    · exact q511_edge9_2
    · exact q511_edge9_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge10_0
    · exact q511_edge10_1
    · exact q511_edge10_2
    · exact q511_edge10_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge11_0
    · exact q511_edge11_1
    · exact q511_edge11_2
    · exact q511_edge11_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge12_0
    · exact q511_edge12_1
    · exact q511_edge12_2
    · exact q511_edge12_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge13_0
    · exact q511_edge13_1
    · exact q511_edge13_2
    · exact q511_edge13_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge14_0
    · exact q511_edge14_1
    · exact q511_edge14_2
    · exact q511_edge14_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge15_0
    · exact q511_edge15_1
    · exact q511_edge15_2
    · exact q511_edge15_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge16_0
    · exact q511_edge16_1
    · exact q511_edge16_2
    · exact q511_edge16_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge17_0
    · exact q511_edge17_1
    · exact q511_edge17_2
    · exact q511_edge17_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge18_0
    · exact q511_edge18_1
    · exact q511_edge18_2
    · exact q511_edge18_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge19_0
    · exact q511_edge19_1
    · exact q511_edge19_2
    · exact q511_edge19_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge20_0
    · exact q511_edge20_1
    · exact q511_edge20_2
    · exact q511_edge20_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge21_0
    · exact q511_edge21_1
    · exact q511_edge21_2
    · exact q511_edge21_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge22_0
    · exact q511_edge22_1
    · exact q511_edge22_2
    · exact q511_edge22_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge23_0
    · exact q511_edge23_1
    · exact q511_edge23_2
    · exact q511_edge23_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge24_0
    · exact q511_edge24_1
    · exact q511_edge24_2
    · exact q511_edge24_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge25_0
    · exact q511_edge25_1
    · exact q511_edge25_2
    · exact q511_edge25_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact q511_edge26_0
    · exact q511_edge26_1
    · exact q511_edge26_2
    · exact q511_edge26_3

theorem q511_checks : Checks BoundedLStarData.q511 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := q511_reachable
  cyclic := q511_cyclic
  strips := by
    intro s
    change Fin 3 at s
    have h : s=0 ∨ s=1 ∨ s=2 := by omega
    rcases h with rfl|rfl|rfl
    · exact q511_strip0
    · exact q511_strip1
    · exact q511_strip2
  edges := q511_edges
  triangles := (decide_eq_true q511_triangles).symm
  descents := fun _ => q511_descents

end QuiverProofs.BoundedLStarChecks
