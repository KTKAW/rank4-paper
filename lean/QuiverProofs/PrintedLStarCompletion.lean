import QuiverProofs.PrintedLStarData
import QuiverProofs.LStarCertificate
import QuiverProofs.E2Certificate
import QuiverProofs.E3Completion

/-! Kernel-checked L_star certificates for the exact printed E1 and E4
representatives. The all-word conclusions use the proved recursive region
semantics, including every actual N/D parent and all label/reversal frames. -/
namespace QuiverProofs.PrintedLStarCompletion
open LStar PrintedLStarData

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem e1_prefix0 : applyWord (PrintedLStarData.e1.node 0) [] = (ofSix (-2) (-2) (1) (-1) (2) (-2)) := by
  rfl

private theorem e1_prefix1 : applyWord (PrintedLStarData.e1.node 0) [0] = (ofSix (2) (2) (-1) (-1) (4) (0)) := by
  rw [show ([0] : List (Fin 4)) = [] ++ [0] from rfl,
    applyWord_append,e1_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix2 : applyWord (PrintedLStarData.e1.node 0) [2] = (ofSix (-2) (2) (-3) (1) (0) (2)) := by
  rw [show ([2] : List (Fin 4)) = [] ++ [2] from rfl,
    applyWord_append,e1_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix3 : applyWord (PrintedLStarData.e1.node 0) [0,1] = (ofSix (-2) (2) (7) (1) (-4) (4)) := by
  rw [show ([0,1] : List (Fin 4)) = [0] ++ [1] from rfl,
    applyWord_append,e1_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix4 : applyWord (PrintedLStarData.e1.node 0) [0,2] = (ofSix (4) (-2) (-1) (1) (4) (0)) := by
  rw [show ([0,2] : List (Fin 4)) = [0] ++ [2] from rfl,
    applyWord_append,e1_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix5 : applyWord (PrintedLStarData.e1.node 0) [0,3] = (ofSix (-2) (2) (1) (-1) (-4) (0)) := by
  rw [show ([0,3] : List (Fin 4)) = [0] ++ [3] from rfl,
    applyWord_append,e1_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix6 : applyWord (PrintedLStarData.e1.node 0) [2,1] = (ofSix (2) (2) (-3) (-1) (0) (2)) := by
  rw [show ([2,1] : List (Fin 4)) = [2] ++ [1] from rfl,
    applyWord_append,e1_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix7 : applyWord (PrintedLStarData.e1.node 0) [2,3] = (ofSix (-2) (-4) (3) (1) (0) (-2)) := by
  rw [show ([2,3] : List (Fin 4)) = [2] ++ [3] from rfl,
    applyWord_append,e1_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix8 : applyWord (PrintedLStarData.e1.node 0) [0,1,2] = (ofSix (-2) (-2) (15) (-1) (0) (-4)) := by
  rw [show ([0,1,2] : List (Fin 4)) = [0,1] ++ [2] from rfl,
    applyWord_append,e1_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix9 : applyWord (PrintedLStarData.e1.node 0) [0,2,0] = (ofSix (-4) (2) (1) (-7) (0) (0)) := by
  rw [show ([0,2,0] : List (Fin 4)) = [0,2] ++ [0] from rfl,
    applyWord_append,e1_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix10 : applyWord (PrintedLStarData.e1.node 0) [0,2,1] = (ofSix (-4) (2) (15) (-1) (-4) (0)) := by
  rw [show ([0,2,1] : List (Fin 4)) = [0,2] ++ [1] from rfl,
    applyWord_append,e1_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix11 : applyWord (PrintedLStarData.e1.node 0) [0,2,3] = (ofSix (0) (-2) (1) (1) (-4) (0)) := by
  rw [show ([0,2,3] : List (Fin 4)) = [0,2] ++ [3] from rfl,
    applyWord_append,e1_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix12 : applyWord (PrintedLStarData.e1.node 0) [0,3,1] = (ofSix (2) (0) (-7) (1) (4) (0)) := by
  rw [show ([0,3,1] : List (Fin 4)) = [0,3] ++ [1] from rfl,
    applyWord_append,e1_prefix5]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix13 : applyWord (PrintedLStarData.e1.node 0) [2,1,3] = (ofSix (2) (-4) (3) (-1) (0) (-2)) := by
  rw [show ([2,1,3] : List (Fin 4)) = [2,1] ++ [3] from rfl,
    applyWord_append,e1_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix14 : applyWord (PrintedLStarData.e1.node 0) [2,3,2] = (ofSix (-6) (4) (-5) (-1) (0) (2)) := by
  rw [show ([2,3,2] : List (Fin 4)) = [2,3] ++ [2] from rfl,
    applyWord_append,e1_prefix7]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix15 : applyWord (PrintedLStarData.e1.node 0) [2,1,3,2] = (ofSix (2) (4) (-5) (1) (-2) (2)) := by
  rw [show ([2,1,3,2] : List (Fin 4)) = [2,1,3] ++ [2] from rfl,
    applyWord_append,e1_prefix13]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_prefix16 : applyWord (PrintedLStarData.e1.node 0) [2,3,2,1] = (ofSix (6) (-2) (-5) (1) (0) (2)) := by
  rw [show ([2,3,2,1] : List (Fin 4)) = [2,3,2] ++ [1] from rfl,
    applyWord_append,e1_prefix14]
  apply entriesEqual_eq
  decide +kernel

private theorem e1_reachable0 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 0).word) (PrintedLStarData.e1.node 0) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) []) (ofSix (-2) (-2) (1) (-1) (2) (-2))
  rw [e1_prefix0]
  intro u v; rfl

private theorem e1_cyclic0 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 0) := by decide +kernel

private theorem e1_edge0_0 :
    EdgeChecks PrintedLStarData.e1 0 0 ((PrintedLStarData.e1.core 0).edges 0) := by decide +kernel

private theorem e1_edge0_1 :
    EdgeChecks PrintedLStarData.e1 0 1 ((PrintedLStarData.e1.core 0).edges 1) := by decide +kernel

private theorem e1_edge0_2 :
    EdgeChecks PrintedLStarData.e1 0 2 ((PrintedLStarData.e1.core 0).edges 2) := by decide +kernel

private theorem e1_edge0_3 :
    EdgeChecks PrintedLStarData.e1 0 3 ((PrintedLStarData.e1.core 0).edges 3) := by decide +kernel

private theorem e1_triangles0 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 0) = true := by decide +kernel

private theorem e1_descent0 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-2) (1) (-1) (2) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable1 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 1).word) (PrintedLStarData.e1.node 1) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0]) (ofSix (2) (2) (-1) (-1) (4) (0))
  rw [e1_prefix1]
  intro u v; rfl

private theorem e1_cyclic1 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 1) := by decide +kernel

private theorem e1_edge1_0 :
    EdgeChecks PrintedLStarData.e1 1 0 ((PrintedLStarData.e1.core 1).edges 0) := by decide +kernel

private theorem e1_edge1_1 :
    EdgeChecks PrintedLStarData.e1 1 1 ((PrintedLStarData.e1.core 1).edges 1) := by decide +kernel

private theorem e1_edge1_2 :
    EdgeChecks PrintedLStarData.e1 1 2 ((PrintedLStarData.e1.core 1).edges 2) := by decide +kernel

private theorem e1_edge1_3 :
    EdgeChecks PrintedLStarData.e1 1 3 ((PrintedLStarData.e1.core 1).edges 3) := by decide +kernel

private theorem e1_triangles1 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 1) = true := by decide +kernel

private theorem e1_descent1 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (2) (-1) (-1) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable2 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 2).word) (PrintedLStarData.e1.node 2) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [2]) (ofSix (-2) (2) (-3) (1) (0) (2))
  rw [e1_prefix2]
  intro u v; rfl

private theorem e1_cyclic2 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 2) := by decide +kernel

private theorem e1_edge2_0 :
    EdgeChecks PrintedLStarData.e1 2 0 ((PrintedLStarData.e1.core 2).edges 0) := by decide +kernel

private theorem e1_edge2_1 :
    EdgeChecks PrintedLStarData.e1 2 1 ((PrintedLStarData.e1.core 2).edges 1) := by decide +kernel

private theorem e1_edge2_2 :
    EdgeChecks PrintedLStarData.e1 2 2 ((PrintedLStarData.e1.core 2).edges 2) := by decide +kernel

private theorem e1_edge2_3 :
    EdgeChecks PrintedLStarData.e1 2 3 ((PrintedLStarData.e1.core 2).edges 3) := by decide +kernel

private theorem e1_triangles2 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 2) = true := by decide +kernel

private theorem e1_descent2 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (2) (-3) (1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable3 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 3).word) (PrintedLStarData.e1.node 3) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,1]) (ofSix (-2) (2) (7) (1) (-4) (4))
  rw [e1_prefix3]
  intro u v; rfl

private theorem e1_cyclic3 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 3) := by decide +kernel

private theorem e1_edge3_0 :
    EdgeChecks PrintedLStarData.e1 3 0 ((PrintedLStarData.e1.core 3).edges 0) := by decide +kernel

private theorem e1_edge3_1 :
    EdgeChecks PrintedLStarData.e1 3 1 ((PrintedLStarData.e1.core 3).edges 1) := by decide +kernel

private theorem e1_edge3_2 :
    EdgeChecks PrintedLStarData.e1 3 2 ((PrintedLStarData.e1.core 3).edges 2) := by decide +kernel

private theorem e1_edge3_3 :
    EdgeChecks PrintedLStarData.e1 3 3 ((PrintedLStarData.e1.core 3).edges 3) := by decide +kernel

private theorem e1_triangles3 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 3) = true := by decide +kernel

private theorem e1_descent3 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (2) (7) (1) (-4) (4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable4 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 4).word) (PrintedLStarData.e1.node 4) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,2]) (ofSix (4) (-2) (-1) (1) (4) (0))
  rw [e1_prefix4]
  intro u v; rfl

private theorem e1_cyclic4 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 4) := by decide +kernel

private theorem e1_edge4_0 :
    EdgeChecks PrintedLStarData.e1 4 0 ((PrintedLStarData.e1.core 4).edges 0) := by decide +kernel

private theorem e1_edge4_1 :
    EdgeChecks PrintedLStarData.e1 4 1 ((PrintedLStarData.e1.core 4).edges 1) := by decide +kernel

private theorem e1_edge4_2 :
    EdgeChecks PrintedLStarData.e1 4 2 ((PrintedLStarData.e1.core 4).edges 2) := by decide +kernel

private theorem e1_edge4_3 :
    EdgeChecks PrintedLStarData.e1 4 3 ((PrintedLStarData.e1.core 4).edges 3) := by decide +kernel

private theorem e1_triangles4 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 4) = true := by decide +kernel

private theorem e1_descent4 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (4) (-2) (-1) (1) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable5 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 5).word) (PrintedLStarData.e1.node 5) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,3]) (ofSix (-2) (2) (1) (-1) (-4) (0))
  rw [e1_prefix5]
  intro u v; rfl

private theorem e1_cyclic5 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 5) := by decide +kernel

private theorem e1_edge5_0 :
    EdgeChecks PrintedLStarData.e1 5 0 ((PrintedLStarData.e1.core 5).edges 0) := by decide +kernel

private theorem e1_edge5_1 :
    EdgeChecks PrintedLStarData.e1 5 1 ((PrintedLStarData.e1.core 5).edges 1) := by decide +kernel

private theorem e1_edge5_2 :
    EdgeChecks PrintedLStarData.e1 5 2 ((PrintedLStarData.e1.core 5).edges 2) := by decide +kernel

private theorem e1_edge5_3 :
    EdgeChecks PrintedLStarData.e1 5 3 ((PrintedLStarData.e1.core 5).edges 3) := by decide +kernel

private theorem e1_triangles5 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 5) = true := by decide +kernel

private theorem e1_descent5 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (2) (1) (-1) (-4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable6 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 6).word) (PrintedLStarData.e1.node 6) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [2,1]) (ofSix (2) (2) (-3) (-1) (0) (2))
  rw [e1_prefix6]
  intro u v; rfl

private theorem e1_cyclic6 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 6) := by decide +kernel

private theorem e1_edge6_0 :
    EdgeChecks PrintedLStarData.e1 6 0 ((PrintedLStarData.e1.core 6).edges 0) := by decide +kernel

private theorem e1_edge6_1 :
    EdgeChecks PrintedLStarData.e1 6 1 ((PrintedLStarData.e1.core 6).edges 1) := by decide +kernel

private theorem e1_edge6_2 :
    EdgeChecks PrintedLStarData.e1 6 2 ((PrintedLStarData.e1.core 6).edges 2) := by decide +kernel

private theorem e1_edge6_3 :
    EdgeChecks PrintedLStarData.e1 6 3 ((PrintedLStarData.e1.core 6).edges 3) := by decide +kernel

private theorem e1_triangles6 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 6) = true := by decide +kernel

private theorem e1_descent6 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (2) (2) (-3) (-1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable7 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 7).word) (PrintedLStarData.e1.node 7) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [2,3]) (ofSix (-2) (-4) (3) (1) (0) (-2))
  rw [e1_prefix7]
  intro u v; rfl

private theorem e1_cyclic7 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 7) := by decide +kernel

private theorem e1_edge7_0 :
    EdgeChecks PrintedLStarData.e1 7 0 ((PrintedLStarData.e1.core 7).edges 0) := by decide +kernel

private theorem e1_edge7_1 :
    EdgeChecks PrintedLStarData.e1 7 1 ((PrintedLStarData.e1.core 7).edges 1) := by decide +kernel

private theorem e1_edge7_2 :
    EdgeChecks PrintedLStarData.e1 7 2 ((PrintedLStarData.e1.core 7).edges 2) := by decide +kernel

private theorem e1_edge7_3 :
    EdgeChecks PrintedLStarData.e1 7 3 ((PrintedLStarData.e1.core 7).edges 3) := by decide +kernel

private theorem e1_triangles7 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 7) = true := by decide +kernel

private theorem e1_descent7 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-4) (3) (1) (0) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable8 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 8).word) (PrintedLStarData.e1.node 8) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,1,2]) (ofSix (-2) (-2) (15) (-1) (0) (-4))
  rw [e1_prefix8]
  intro u v; rfl

private theorem e1_cyclic8 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 8) := by decide +kernel

private theorem e1_edge8_0 :
    EdgeChecks PrintedLStarData.e1 8 0 ((PrintedLStarData.e1.core 8).edges 0) := by decide +kernel

private theorem e1_edge8_1 :
    EdgeChecks PrintedLStarData.e1 8 1 ((PrintedLStarData.e1.core 8).edges 1) := by decide +kernel

private theorem e1_edge8_2 :
    EdgeChecks PrintedLStarData.e1 8 2 ((PrintedLStarData.e1.core 8).edges 2) := by decide +kernel

private theorem e1_edge8_3 :
    EdgeChecks PrintedLStarData.e1 8 3 ((PrintedLStarData.e1.core 8).edges 3) := by decide +kernel

private theorem e1_triangles8 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 8) = true := by decide +kernel

private theorem e1_descent8 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-2) (15) (-1) (0) (-4)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable9 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 9).word) (PrintedLStarData.e1.node 9) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,2,0]) (ofSix (-4) (2) (1) (-7) (0) (0))
  rw [e1_prefix9]
  intro u v; rfl

private theorem e1_cyclic9 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 9) := by decide +kernel

private theorem e1_edge9_0 :
    EdgeChecks PrintedLStarData.e1 9 0 ((PrintedLStarData.e1.core 9).edges 0) := by decide +kernel

private theorem e1_edge9_1 :
    EdgeChecks PrintedLStarData.e1 9 1 ((PrintedLStarData.e1.core 9).edges 1) := by decide +kernel

private theorem e1_edge9_2 :
    EdgeChecks PrintedLStarData.e1 9 2 ((PrintedLStarData.e1.core 9).edges 2) := by decide +kernel

private theorem e1_edge9_3 :
    EdgeChecks PrintedLStarData.e1 9 3 ((PrintedLStarData.e1.core 9).edges 3) := by decide +kernel

private theorem e1_triangles9 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 9) = true := by decide +kernel

private theorem e1_descent9 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (-4) (2) (1) (-7) (0) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable10 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 10).word) (PrintedLStarData.e1.node 10) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,2,1]) (ofSix (-4) (2) (15) (-1) (-4) (0))
  rw [e1_prefix10]
  intro u v; rfl

private theorem e1_cyclic10 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 10) := by decide +kernel

private theorem e1_edge10_0 :
    EdgeChecks PrintedLStarData.e1 10 0 ((PrintedLStarData.e1.core 10).edges 0) := by decide +kernel

private theorem e1_edge10_1 :
    EdgeChecks PrintedLStarData.e1 10 1 ((PrintedLStarData.e1.core 10).edges 1) := by decide +kernel

private theorem e1_edge10_2 :
    EdgeChecks PrintedLStarData.e1 10 2 ((PrintedLStarData.e1.core 10).edges 2) := by decide +kernel

private theorem e1_edge10_3 :
    EdgeChecks PrintedLStarData.e1 10 3 ((PrintedLStarData.e1.core 10).edges 3) := by decide +kernel

private theorem e1_triangles10 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 10) = true := by decide +kernel

private theorem e1_descent10 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 10) = true := by
  change allTriangleDescentsCheck (ofSix (-4) (2) (15) (-1) (-4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable11 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 11).word) (PrintedLStarData.e1.node 11) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,2,3]) (ofSix (0) (-2) (1) (1) (-4) (0))
  rw [e1_prefix11]
  intro u v; rfl

private theorem e1_cyclic11 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 11) := by decide +kernel

private theorem e1_edge11_0 :
    EdgeChecks PrintedLStarData.e1 11 0 ((PrintedLStarData.e1.core 11).edges 0) := by decide +kernel

private theorem e1_edge11_1 :
    EdgeChecks PrintedLStarData.e1 11 1 ((PrintedLStarData.e1.core 11).edges 1) := by decide +kernel

private theorem e1_edge11_2 :
    EdgeChecks PrintedLStarData.e1 11 2 ((PrintedLStarData.e1.core 11).edges 2) := by decide +kernel

private theorem e1_edge11_3 :
    EdgeChecks PrintedLStarData.e1 11 3 ((PrintedLStarData.e1.core 11).edges 3) := by decide +kernel

private theorem e1_triangles11 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 11) = true := by decide +kernel

private theorem e1_descent11 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 11) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-2) (1) (1) (-4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable12 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 12).word) (PrintedLStarData.e1.node 12) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [0,3,1]) (ofSix (2) (0) (-7) (1) (4) (0))
  rw [e1_prefix12]
  intro u v; rfl

private theorem e1_cyclic12 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 12) := by decide +kernel

private theorem e1_edge12_0 :
    EdgeChecks PrintedLStarData.e1 12 0 ((PrintedLStarData.e1.core 12).edges 0) := by decide +kernel

private theorem e1_edge12_1 :
    EdgeChecks PrintedLStarData.e1 12 1 ((PrintedLStarData.e1.core 12).edges 1) := by decide +kernel

private theorem e1_edge12_2 :
    EdgeChecks PrintedLStarData.e1 12 2 ((PrintedLStarData.e1.core 12).edges 2) := by decide +kernel

private theorem e1_edge12_3 :
    EdgeChecks PrintedLStarData.e1 12 3 ((PrintedLStarData.e1.core 12).edges 3) := by decide +kernel

private theorem e1_triangles12 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 12) = true := by decide +kernel

private theorem e1_descent12 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 12) = true := by
  change allTriangleDescentsCheck (ofSix (2) (0) (-7) (1) (4) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable13 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 13).word) (PrintedLStarData.e1.node 13) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [2,1,3]) (ofSix (2) (-4) (3) (-1) (0) (-2))
  rw [e1_prefix13]
  intro u v; rfl

private theorem e1_cyclic13 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 13) := by decide +kernel

private theorem e1_edge13_0 :
    EdgeChecks PrintedLStarData.e1 13 0 ((PrintedLStarData.e1.core 13).edges 0) := by decide +kernel

private theorem e1_edge13_1 :
    EdgeChecks PrintedLStarData.e1 13 1 ((PrintedLStarData.e1.core 13).edges 1) := by decide +kernel

private theorem e1_edge13_2 :
    EdgeChecks PrintedLStarData.e1 13 2 ((PrintedLStarData.e1.core 13).edges 2) := by decide +kernel

private theorem e1_edge13_3 :
    EdgeChecks PrintedLStarData.e1 13 3 ((PrintedLStarData.e1.core 13).edges 3) := by decide +kernel

private theorem e1_triangles13 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 13) = true := by decide +kernel

private theorem e1_descent13 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 13) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-4) (3) (-1) (0) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable14 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 14).word) (PrintedLStarData.e1.node 14) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [2,3,2]) (ofSix (-6) (4) (-5) (-1) (0) (2))
  rw [e1_prefix14]
  intro u v; rfl

private theorem e1_cyclic14 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 14) := by decide +kernel

private theorem e1_edge14_0 :
    EdgeChecks PrintedLStarData.e1 14 0 ((PrintedLStarData.e1.core 14).edges 0) := by decide +kernel

private theorem e1_edge14_1 :
    EdgeChecks PrintedLStarData.e1 14 1 ((PrintedLStarData.e1.core 14).edges 1) := by decide +kernel

private theorem e1_edge14_2 :
    EdgeChecks PrintedLStarData.e1 14 2 ((PrintedLStarData.e1.core 14).edges 2) := by decide +kernel

private theorem e1_edge14_3 :
    EdgeChecks PrintedLStarData.e1 14 3 ((PrintedLStarData.e1.core 14).edges 3) := by decide +kernel

private theorem e1_triangles14 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 14) = true := by decide +kernel

private theorem e1_descent14 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 14) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (4) (-5) (-1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable15 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 15).word) (PrintedLStarData.e1.node 15) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [2,1,3,2]) (ofSix (2) (4) (-5) (1) (-2) (2))
  rw [e1_prefix15]
  intro u v; rfl

private theorem e1_cyclic15 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 15) := by decide +kernel

private theorem e1_edge15_0 :
    EdgeChecks PrintedLStarData.e1 15 0 ((PrintedLStarData.e1.core 15).edges 0) := by decide +kernel

private theorem e1_edge15_1 :
    EdgeChecks PrintedLStarData.e1 15 1 ((PrintedLStarData.e1.core 15).edges 1) := by decide +kernel

private theorem e1_edge15_2 :
    EdgeChecks PrintedLStarData.e1 15 2 ((PrintedLStarData.e1.core 15).edges 2) := by decide +kernel

private theorem e1_edge15_3 :
    EdgeChecks PrintedLStarData.e1 15 3 ((PrintedLStarData.e1.core 15).edges 3) := by decide +kernel

private theorem e1_triangles15 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 15) = true := by decide +kernel

private theorem e1_descent15 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 15) = true := by
  change allTriangleDescentsCheck (ofSix (2) (4) (-5) (1) (-2) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e1_reachable16 :
    EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core 16).word) (PrintedLStarData.e1.node 16) := by
  change EntriesEqual (applyWord (PrintedLStarData.e1.node 0) [2,3,2,1]) (ofSix (6) (-2) (-5) (1) (0) (2))
  rw [e1_prefix16]
  intro u v; rfl

private theorem e1_cyclic16 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node 16) := by decide +kernel

private theorem e1_edge16_0 :
    EdgeChecks PrintedLStarData.e1 16 0 ((PrintedLStarData.e1.core 16).edges 0) := by decide +kernel

private theorem e1_edge16_1 :
    EdgeChecks PrintedLStarData.e1 16 1 ((PrintedLStarData.e1.core 16).edges 1) := by decide +kernel

private theorem e1_edge16_2 :
    EdgeChecks PrintedLStarData.e1 16 2 ((PrintedLStarData.e1.core 16).edges 2) := by decide +kernel

private theorem e1_edge16_3 :
    EdgeChecks PrintedLStarData.e1 16 3 ((PrintedLStarData.e1.core 16).edges 3) := by decide +kernel

private theorem e1_triangles16 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node 16) = true := by decide +kernel

private theorem e1_descent16 :
    allTriangleDescentsCheck (PrintedLStarData.e1.node 16) = true := by
  change allTriangleDescentsCheck (ofSix (6) (-2) (-5) (1) (0) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem e1_reachable : ∀ i, EntriesEqual (applyWord (PrintedLStarData.e1.node 0) (PrintedLStarData.e1.core i).word) (PrintedLStarData.e1.node i) := by
  intro i
  change Fin 17 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact e1_reachable0
  · exact e1_reachable1
  · exact e1_reachable2
  · exact e1_reachable3
  · exact e1_reachable4
  · exact e1_reachable5
  · exact e1_reachable6
  · exact e1_reachable7
  · exact e1_reachable8
  · exact e1_reachable9
  · exact e1_reachable10
  · exact e1_reachable11
  · exact e1_reachable12
  · exact e1_reachable13
  · exact e1_reachable14
  · exact e1_reachable15
  · exact e1_reachable16

theorem e1_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e1.node i) := by
  intro i
  change Fin 17 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact e1_cyclic0
  · exact e1_cyclic1
  · exact e1_cyclic2
  · exact e1_cyclic3
  · exact e1_cyclic4
  · exact e1_cyclic5
  · exact e1_cyclic6
  · exact e1_cyclic7
  · exact e1_cyclic8
  · exact e1_cyclic9
  · exact e1_cyclic10
  · exact e1_cyclic11
  · exact e1_cyclic12
  · exact e1_cyclic13
  · exact e1_cyclic14
  · exact e1_cyclic15
  · exact e1_cyclic16

theorem e1_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e1.node i) = true := by
  intro i
  change Fin 17 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact e1_triangles0
  · exact e1_triangles1
  · exact e1_triangles2
  · exact e1_triangles3
  · exact e1_triangles4
  · exact e1_triangles5
  · exact e1_triangles6
  · exact e1_triangles7
  · exact e1_triangles8
  · exact e1_triangles9
  · exact e1_triangles10
  · exact e1_triangles11
  · exact e1_triangles12
  · exact e1_triangles13
  · exact e1_triangles14
  · exact e1_triangles15
  · exact e1_triangles16

theorem e1_descents : ∀ i, allTriangleDescentsCheck (PrintedLStarData.e1.node i) = true := by
  intro i
  change Fin 17 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact e1_descent0
  · exact e1_descent1
  · exact e1_descent2
  · exact e1_descent3
  · exact e1_descent4
  · exact e1_descent5
  · exact e1_descent6
  · exact e1_descent7
  · exact e1_descent8
  · exact e1_descent9
  · exact e1_descent10
  · exact e1_descent11
  · exact e1_descent12
  · exact e1_descent13
  · exact e1_descent14
  · exact e1_descent15
  · exact e1_descent16

theorem e1_edges : ∀ i k, EdgeChecks PrintedLStarData.e1 i k ((PrintedLStarData.e1.core i).edges k) := by
  intro i k
  change Fin 17 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge0_0
    · exact e1_edge0_1
    · exact e1_edge0_2
    · exact e1_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge1_0
    · exact e1_edge1_1
    · exact e1_edge1_2
    · exact e1_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge2_0
    · exact e1_edge2_1
    · exact e1_edge2_2
    · exact e1_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge3_0
    · exact e1_edge3_1
    · exact e1_edge3_2
    · exact e1_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge4_0
    · exact e1_edge4_1
    · exact e1_edge4_2
    · exact e1_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge5_0
    · exact e1_edge5_1
    · exact e1_edge5_2
    · exact e1_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge6_0
    · exact e1_edge6_1
    · exact e1_edge6_2
    · exact e1_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge7_0
    · exact e1_edge7_1
    · exact e1_edge7_2
    · exact e1_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge8_0
    · exact e1_edge8_1
    · exact e1_edge8_2
    · exact e1_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge9_0
    · exact e1_edge9_1
    · exact e1_edge9_2
    · exact e1_edge9_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge10_0
    · exact e1_edge10_1
    · exact e1_edge10_2
    · exact e1_edge10_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge11_0
    · exact e1_edge11_1
    · exact e1_edge11_2
    · exact e1_edge11_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge12_0
    · exact e1_edge12_1
    · exact e1_edge12_2
    · exact e1_edge12_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge13_0
    · exact e1_edge13_1
    · exact e1_edge13_2
    · exact e1_edge13_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge14_0
    · exact e1_edge14_1
    · exact e1_edge14_2
    · exact e1_edge14_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge15_0
    · exact e1_edge15_1
    · exact e1_edge15_2
    · exact e1_edge15_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e1_edge16_0
    · exact e1_edge16_1
    · exact e1_edge16_2
    · exact e1_edge16_3

theorem e1_checks : Checks PrintedLStarData.e1 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := e1_reachable
  cyclic := e1_cyclic
  strips := by
    intro s
    change Fin 0 at s
    exact Fin.elim0 s
  edges := e1_edges
  triangles := (decide_eq_true e1_triangles).symm
  descents := fun _ => e1_descents

theorem e1_accepted : accept e1 = true := (accept_iff e1).mpr e1_checks

open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem e4_prefix0 : applyWord (PrintedLStarData.e4.node 0) [] = (ofSix (-2) (-1) (2) (-2) (-1) (-2)) := by
  rfl

private theorem e4_prefix1 : applyWord (PrintedLStarData.e4.node 0) [0] = (ofSix (2) (1) (-2) (-2) (3) (0)) := by
  rw [show ([0] : List (Fin 4)) = [] ++ [0] from rfl,
    applyWord_append,e4_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem e4_prefix2 : applyWord (PrintedLStarData.e4.node 0) [1] = (ofSix (2) (-5) (0) (2) (1) (-2)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,e4_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem e4_prefix3 : applyWord (PrintedLStarData.e4.node 0) [0,2] = (ofSix (4) (-1) (-2) (2) (3) (0)) := by
  rw [show ([0,2] : List (Fin 4)) = [0] ++ [2] from rfl,
    applyWord_append,e4_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem e4_prefix4 : applyWord (PrintedLStarData.e4.node 0) [1,3] = (ofSix (2) (-5) (0) (4) (-1) (2)) := by
  rw [show ([1,3] : List (Fin 4)) = [1] ++ [3] from rfl,
    applyWord_append,e4_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem e4_reachable0 :
    EntriesEqual (applyWord (PrintedLStarData.e4.node 0) (PrintedLStarData.e4.core 0).word) (PrintedLStarData.e4.node 0) := by
  change EntriesEqual (applyWord (PrintedLStarData.e4.node 0) []) (ofSix (-2) (-1) (2) (-2) (-1) (-2))
  rw [e4_prefix0]
  intro u v; rfl

private theorem e4_cyclic0 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e4.node 0) := by decide +kernel

private theorem e4_edge0_0 :
    EdgeChecks PrintedLStarData.e4 0 0 ((PrintedLStarData.e4.core 0).edges 0) := by decide +kernel

private theorem e4_edge0_1 :
    EdgeChecks PrintedLStarData.e4 0 1 ((PrintedLStarData.e4.core 0).edges 1) := by decide +kernel

private theorem e4_edge0_2 :
    EdgeChecks PrintedLStarData.e4 0 2 ((PrintedLStarData.e4.core 0).edges 2) := by decide +kernel

private theorem e4_edge0_3 :
    EdgeChecks PrintedLStarData.e4 0 3 ((PrintedLStarData.e4.core 0).edges 3) := by decide +kernel

private theorem e4_triangles0 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e4.node 0) = true := by decide +kernel

private theorem e4_descent0 :
    allTriangleDescentsCheck (PrintedLStarData.e4.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-1) (2) (-2) (-1) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e4_reachable1 :
    EntriesEqual (applyWord (PrintedLStarData.e4.node 0) (PrintedLStarData.e4.core 1).word) (PrintedLStarData.e4.node 1) := by
  change EntriesEqual (applyWord (PrintedLStarData.e4.node 0) [0]) (ofSix (2) (1) (-2) (-2) (3) (0))
  rw [e4_prefix1]
  intro u v; rfl

private theorem e4_cyclic1 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e4.node 1) := by decide +kernel

private theorem e4_edge1_0 :
    EdgeChecks PrintedLStarData.e4 1 0 ((PrintedLStarData.e4.core 1).edges 0) := by decide +kernel

private theorem e4_edge1_1 :
    EdgeChecks PrintedLStarData.e4 1 1 ((PrintedLStarData.e4.core 1).edges 1) := by decide +kernel

private theorem e4_edge1_2 :
    EdgeChecks PrintedLStarData.e4 1 2 ((PrintedLStarData.e4.core 1).edges 2) := by decide +kernel

private theorem e4_edge1_3 :
    EdgeChecks PrintedLStarData.e4 1 3 ((PrintedLStarData.e4.core 1).edges 3) := by decide +kernel

private theorem e4_triangles1 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e4.node 1) = true := by decide +kernel

private theorem e4_descent1 :
    allTriangleDescentsCheck (PrintedLStarData.e4.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (2) (1) (-2) (-2) (3) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e4_reachable2 :
    EntriesEqual (applyWord (PrintedLStarData.e4.node 0) (PrintedLStarData.e4.core 2).word) (PrintedLStarData.e4.node 2) := by
  change EntriesEqual (applyWord (PrintedLStarData.e4.node 0) [1]) (ofSix (2) (-5) (0) (2) (1) (-2))
  rw [e4_prefix2]
  intro u v; rfl

private theorem e4_cyclic2 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e4.node 2) := by decide +kernel

private theorem e4_edge2_0 :
    EdgeChecks PrintedLStarData.e4 2 0 ((PrintedLStarData.e4.core 2).edges 0) := by decide +kernel

private theorem e4_edge2_1 :
    EdgeChecks PrintedLStarData.e4 2 1 ((PrintedLStarData.e4.core 2).edges 1) := by decide +kernel

private theorem e4_edge2_2 :
    EdgeChecks PrintedLStarData.e4 2 2 ((PrintedLStarData.e4.core 2).edges 2) := by decide +kernel

private theorem e4_edge2_3 :
    EdgeChecks PrintedLStarData.e4 2 3 ((PrintedLStarData.e4.core 2).edges 3) := by decide +kernel

private theorem e4_triangles2 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e4.node 2) = true := by decide +kernel

private theorem e4_descent2 :
    allTriangleDescentsCheck (PrintedLStarData.e4.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-5) (0) (2) (1) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e4_reachable3 :
    EntriesEqual (applyWord (PrintedLStarData.e4.node 0) (PrintedLStarData.e4.core 3).word) (PrintedLStarData.e4.node 3) := by
  change EntriesEqual (applyWord (PrintedLStarData.e4.node 0) [0,2]) (ofSix (4) (-1) (-2) (2) (3) (0))
  rw [e4_prefix3]
  intro u v; rfl

private theorem e4_cyclic3 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e4.node 3) := by decide +kernel

private theorem e4_edge3_0 :
    EdgeChecks PrintedLStarData.e4 3 0 ((PrintedLStarData.e4.core 3).edges 0) := by decide +kernel

private theorem e4_edge3_1 :
    EdgeChecks PrintedLStarData.e4 3 1 ((PrintedLStarData.e4.core 3).edges 1) := by decide +kernel

private theorem e4_edge3_2 :
    EdgeChecks PrintedLStarData.e4 3 2 ((PrintedLStarData.e4.core 3).edges 2) := by decide +kernel

private theorem e4_edge3_3 :
    EdgeChecks PrintedLStarData.e4 3 3 ((PrintedLStarData.e4.core 3).edges 3) := by decide +kernel

private theorem e4_triangles3 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e4.node 3) = true := by decide +kernel

private theorem e4_descent3 :
    allTriangleDescentsCheck (PrintedLStarData.e4.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (4) (-1) (-2) (2) (3) (0)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem e4_reachable4 :
    EntriesEqual (applyWord (PrintedLStarData.e4.node 0) (PrintedLStarData.e4.core 4).word) (PrintedLStarData.e4.node 4) := by
  change EntriesEqual (applyWord (PrintedLStarData.e4.node 0) [1,3]) (ofSix (2) (-5) (0) (4) (-1) (2))
  rw [e4_prefix4]
  intro u v; rfl

private theorem e4_cyclic4 : ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e4.node 4) := by decide +kernel

private theorem e4_edge4_0 :
    EdgeChecks PrintedLStarData.e4 4 0 ((PrintedLStarData.e4.core 4).edges 0) := by decide +kernel

private theorem e4_edge4_1 :
    EdgeChecks PrintedLStarData.e4 4 1 ((PrintedLStarData.e4.core 4).edges 1) := by decide +kernel

private theorem e4_edge4_2 :
    EdgeChecks PrintedLStarData.e4 4 2 ((PrintedLStarData.e4.core 4).edges 2) := by decide +kernel

private theorem e4_edge4_3 :
    EdgeChecks PrintedLStarData.e4 4 3 ((PrintedLStarData.e4.core 4).edges 3) := by decide +kernel

private theorem e4_triangles4 :
    TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e4.node 4) = true := by decide +kernel

private theorem e4_descent4 :
    allTriangleDescentsCheck (PrintedLStarData.e4.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-5) (0) (4) (-1) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

theorem e4_reachable : ∀ i, EntriesEqual (applyWord (PrintedLStarData.e4.node 0) (PrintedLStarData.e4.core i).word) (PrintedLStarData.e4.node i) := by
  intro i
  change Fin 5 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact e4_reachable0
  · exact e4_reachable1
  · exact e4_reachable2
  · exact e4_reachable3
  · exact e4_reachable4

theorem e4_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (PrintedLStarData.e4.node i) := by
  intro i
  change Fin 5 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact e4_cyclic0
  · exact e4_cyclic1
  · exact e4_cyclic2
  · exact e4_cyclic3
  · exact e4_cyclic4

theorem e4_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (PrintedLStarData.e4.node i) = true := by
  intro i
  change Fin 5 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact e4_triangles0
  · exact e4_triangles1
  · exact e4_triangles2
  · exact e4_triangles3
  · exact e4_triangles4

theorem e4_descents : ∀ i, allTriangleDescentsCheck (PrintedLStarData.e4.node i) = true := by
  intro i
  change Fin 5 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact e4_descent0
  · exact e4_descent1
  · exact e4_descent2
  · exact e4_descent3
  · exact e4_descent4

theorem e4_edges : ∀ i k, EdgeChecks PrintedLStarData.e4 i k ((PrintedLStarData.e4.core i).edges k) := by
  intro i k
  change Fin 5 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e4_edge0_0
    · exact e4_edge0_1
    · exact e4_edge0_2
    · exact e4_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e4_edge1_0
    · exact e4_edge1_1
    · exact e4_edge1_2
    · exact e4_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e4_edge2_0
    · exact e4_edge2_1
    · exact e4_edge2_2
    · exact e4_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e4_edge3_0
    · exact e4_edge3_1
    · exact e4_edge3_2
    · exact e4_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact e4_edge4_0
    · exact e4_edge4_1
    · exact e4_edge4_2
    · exact e4_edge4_3

theorem e4_checks : Checks PrintedLStarData.e4 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := e4_reachable
  cyclic := e4_cyclic
  strips := by
    intro s
    change Fin 0 at s
    exact Fin.elim0 s
  edges := e4_edges
  triangles := (decide_eq_true e4_triangles).symm
  descents := fun _ => e4_descents

theorem e4_accepted : accept e4 = true := (accept_iff e4).mpr e4_checks

/-- Exact source `sequel_research/certificates/q196.json`. -/
theorem nma_q196 : ¬MutationAcyclic (ofSix (-2) (-2) 1 (-1) 2 (-2)) :=
  accept_NMA e1 e1_accepted

/-- Exact source `sequel_research/certificates/q498.json`. -/
theorem nma_q498 : ¬MutationAcyclic (ofSix (-2) (-1) 2 (-2) (-1) (-2)) :=
  accept_NMA e4 e4_accepted

theorem E1_NMA : ¬MutationAcyclic (ClassSeparation.printed 0) := nma_q196

theorem E4_NMA : ¬MutationAcyclic (ClassSeparation.printed 3) := nma_q498

theorem E1_global_triangle_avoidance (word : List (Fin 4)) :
    TriangleRegions.AllTrianglesMA (applyWord (ClassSeparation.printed 0) word) :=
  accept_global_triangles e1 e1_accepted rfl word

theorem E4_global_triangle_avoidance (word : List (Fin 4)) :
    TriangleRegions.AllTrianglesMA (applyWord (ClassSeparation.printed 3) word) :=
  accept_global_triangles e4 e4_accepted rfl word

theorem E1_structural_package :
    ¬MutationAcyclic (ClassSeparation.printed 0) ∧
    ∀ word : List (Fin 4), TriangleRegions.AllTrianglesMA
      (applyWord (ClassSeparation.printed 0) word) :=
  ⟨E1_NMA,E1_global_triangle_avoidance⟩

theorem E4_structural_package :
    ¬MutationAcyclic (ClassSeparation.printed 3) ∧
    ∀ word : List (Fin 4), TriangleRegions.AllTrianglesMA
      (applyWord (ClassSeparation.printed 3) word) :=
  ⟨E4_NMA,E4_global_triangle_avoidance⟩

/-- Each of the four printed exceptional representatives is unconditionally
NMA, with no proper-order existence or endpoint hypothesis. -/
theorem four_printed_NMA (i : Fin 4) :
    ¬MutationAcyclic (ClassSeparation.printed (Fin.castLE (by decide) i)) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl
  · exact E1_NMA
  · exact E2Certificate.E2_NMA
  · exact E3Completion.printed_E3_NMA
  · exact E4_NMA

/-- Every induced triangle in every descendant of each of the four printed
exceptions is mutation-acyclic. -/
theorem four_printed_global_triangle_avoidance (i : Fin 4) (word : List (Fin 4)) :
    TriangleRegions.AllTrianglesMA
      (applyWord (ClassSeparation.printed (Fin.castLE (by decide) i)) word) := by
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl
  · exact E1_global_triangle_avoidance word
  · exact E2Certificate.E2_global_triangle_avoidance word
  · exact E3Completion.E3_global_triangle_avoidance word
  · exact E4_global_triangle_avoidance word

theorem four_printed_structural_package (i : Fin 4) :
    ¬MutationAcyclic (ClassSeparation.printed (Fin.castLE (by decide) i)) ∧
    ∀ word : List (Fin 4), TriangleRegions.AllTrianglesMA
      (applyWord (ClassSeparation.printed (Fin.castLE (by decide) i)) word) :=
  ⟨four_printed_NMA i,four_printed_global_triangle_avoidance i⟩

end QuiverProofs.PrintedLStarCompletion
