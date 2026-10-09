import QuiverProofs.LStarCertificate
import QuiverProofs.WitnessLStarData

namespace QuiverProofs.WitnessLStarDelayed
set_option linter.unusedSimpArgs false
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

private theorem delayed_prefix0 : applyWord (WitnessLStarData.delayed.node 0) [] = (ofSix (0) (-1) (3) (-2) (-2) (-2)) := by
  rfl

private theorem delayed_prefix1 : applyWord (WitnessLStarData.delayed.node 0) [0] = (ofSix (0) (1) (-3) (-2) (-2) (1)) := by
  rw [show ([0] : List (Fin 4)) = [] ++ [0] from rfl,
    applyWord_append,delayed_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix2 : applyWord (WitnessLStarData.delayed.node 0) [1] = (ofSix (0) (-1) (3) (2) (2) (-2)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,delayed_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix3 : applyWord (WitnessLStarData.delayed.node 0) [2] = (ofSix (0) (1) (1) (2) (-6) (2)) := by
  rw [show ([2] : List (Fin 4)) = [] ++ [2] from rfl,
    applyWord_append,delayed_prefix0]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix4 : applyWord (WitnessLStarData.delayed.node 0) [0,1] = (ofSix (0) (1) (-3) (2) (2) (1)) := by
  rw [show ([0,1] : List (Fin 4)) = [0] ++ [1] from rfl,
    applyWord_append,delayed_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix5 : applyWord (WitnessLStarData.delayed.node 0) [0,2] = (ofSix (2) (-1) (-2) (2) (-2) (-1)) := by
  rw [show ([0,2] : List (Fin 4)) = [0] ++ [2] from rfl,
    applyWord_append,delayed_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix6 : applyWord (WitnessLStarData.delayed.node 0) [0,3] = (ofSix (0) (-2) (3) (-4) (2) (-1)) := by
  rw [show ([0,3] : List (Fin 4)) = [0] ++ [3] from rfl,
    applyWord_append,delayed_prefix1]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix7 : applyWord (WitnessLStarData.delayed.node 0) [1,2] = (ofSix (-2) (1) (1) (-2) (2) (2)) := by
  rw [show ([1,2] : List (Fin 4)) = [1] ++ [2] from rfl,
    applyWord_append,delayed_prefix2]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix8 : applyWord (WitnessLStarData.delayed.node 0) [2,0] = (ofSix (0) (-1) (-1) (2) (-6) (2)) := by
  rw [show ([2,0] : List (Fin 4)) = [2] ++ [0] from rfl,
    applyWord_append,delayed_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix9 : applyWord (WitnessLStarData.delayed.node 0) [2,1] = (ofSix (0) (1) (1) (-2) (6) (-10)) := by
  rw [show ([2,1] : List (Fin 4)) = [2] ++ [1] from rfl,
    applyWord_append,delayed_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix10 : applyWord (WitnessLStarData.delayed.node 0) [2,3] = (ofSix (6) (1) (-1) (-10) (6) (-2)) := by
  rw [show ([2,3] : List (Fin 4)) = [2] ++ [3] from rfl,
    applyWord_append,delayed_prefix3]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix11 : applyWord (WitnessLStarData.delayed.node 0) [0,1,2] = (ofSix (0) (-1) (-2) (-2) (4) (-1)) := by
  rw [show ([0,1,2] : List (Fin 4)) = [0,1] ++ [2] from rfl,
    applyWord_append,delayed_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix12 : applyWord (WitnessLStarData.delayed.node 0) [0,1,3] = (ofSix (-6) (-2) (3) (2) (-2) (-1)) := by
  rw [show ([0,1,3] : List (Fin 4)) = [0,1] ++ [3] from rfl,
    applyWord_append,delayed_prefix4]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix13 : applyWord (WitnessLStarData.delayed.node 0) [0,3,0] = (ofSix (0) (2) (-3) (-4) (2) (5)) := by
  rw [show ([0,3,0] : List (Fin 4)) = [0,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix14 : applyWord (WitnessLStarData.delayed.node 0) [0,3,1] = (ofSix (0) (-2) (3) (4) (-2) (7)) := by
  rw [show ([0,3,1] : List (Fin 4)) = [0,3] ++ [1] from rfl,
    applyWord_append,delayed_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix15 : applyWord (WitnessLStarData.delayed.node 0) [0,3,2] = (ofSix (0) (2) (1) (4) (-2) (1)) := by
  rw [show ([0,3,2] : List (Fin 4)) = [0,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix6]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix16 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1] = (ofSix (0) (-1) (-1) (-2) (6) (-10)) := by
  rw [show ([2,0,1] : List (Fin 4)) = [2,0] ++ [1] from rfl,
    applyWord_append,delayed_prefix8]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix17 : applyWord (WitnessLStarData.delayed.node 0) [2,0,3] = (ofSix (0) (-3) (1) (-10) (6) (-2)) := by
  rw [show ([2,0,3] : List (Fin 4)) = [2,0] ++ [3] from rfl,
    applyWord_append,delayed_prefix8]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix18 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2] = (ofSix (2) (-1) (1) (2) (-14) (10)) := by
  rw [show ([2,1,2] : List (Fin 4)) = [2,1] ++ [2] from rfl,
    applyWord_append,delayed_prefix9]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix19 : applyWord (WitnessLStarData.delayed.node 0) [2,1,3] = (ofSix (0) (11) (-1) (58) (-6) (10)) := by
  rw [show ([2,1,3] : List (Fin 4)) = [2,1] ++ [3] from rfl,
    applyWord_append,delayed_prefix9]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix20 : applyWord (WitnessLStarData.delayed.node 0) [2,3,0] = (ofSix (-6) (-1) (1) (-10) (0) (-3)) := by
  rw [show ([2,3,0] : List (Fin 4)) = [2,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix10]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix21 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2] = (ofSix (16) (-1) (-1) (10) (-14) (2)) := by
  rw [show ([2,3,2] : List (Fin 4)) = [2,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix10]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix22 : applyWord (WitnessLStarData.delayed.node 0) [0,1,2,1] = (ofSix (0) (-1) (-2) (2) (-4) (7)) := by
  rw [show ([0,1,2,1] : List (Fin 4)) = [0,1,2] ++ [1] from rfl,
    applyWord_append,delayed_prefix11]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix23 : applyWord (WitnessLStarData.delayed.node 0) [0,1,2,3] = (ofSix (-8) (-1) (2) (2) (-4) (1)) := by
  rw [show ([0,1,2,3] : List (Fin 4)) = [0,1,2] ++ [3] from rfl,
    applyWord_append,delayed_prefix11]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix24 : applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2] = (ofSix (-10) (2) (1) (-2) (-2) (1)) := by
  rw [show ([0,1,3,2] : List (Fin 4)) = [0,1,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix12]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix25 : applyWord (WitnessLStarData.delayed.node 0) [0,3,0,1] = (ofSix (0) (2) (-3) (4) (-2) (13)) := by
  rw [show ([0,3,0,1] : List (Fin 4)) = [0,3,0] ++ [1] from rfl,
    applyWord_append,delayed_prefix13]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix26 : applyWord (WitnessLStarData.delayed.node 0) [0,3,2,1] = (ofSix (0) (2) (1) (-4) (2) (-7)) := by
  rw [show ([0,3,2,1] : List (Fin 4)) = [0,3,2] ++ [1] from rfl,
    applyWord_append,delayed_prefix15]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix27 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,2] = (ofSix (0) (1) (-11) (2) (-14) (10)) := by
  rw [show ([2,0,1,2] : List (Fin 4)) = [2,0,1] ++ [2] from rfl,
    applyWord_append,delayed_prefix16]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix28 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3] = (ofSix (-6) (-1) (1) (58) (-6) (10)) := by
  rw [show ([2,0,1,3] : List (Fin 4)) = [2,0,1] ++ [3] from rfl,
    applyWord_append,delayed_prefix16]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix29 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,0] = (ofSix (-2) (1) (-1) (0) (-14) (11)) := by
  rw [show ([2,1,2,0] : List (Fin 4)) = [2,1,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix18]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix30 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3] = (ofSix (16) (-1) (-1) (-138) (14) (-10)) := by
  rw [show ([2,1,2,3] : List (Fin 4)) = [2,1,2] ++ [3] from rfl,
    applyWord_append,delayed_prefix18]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix31 : applyWord (WitnessLStarData.delayed.node 0) [2,1,3,0] = (ofSix (0) (-11) (1) (58) (-6) (-1)) := by
  rw [show ([2,1,3,0] : List (Fin 4)) = [2,1,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix19]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix32 : applyWord (WitnessLStarData.delayed.node 0) [2,3,0,2] = (ofSix (-6) (1) (-2) (10) (-30) (3)) := by
  rw [show ([2,3,0,2] : List (Fin 4)) = [2,3,0] ++ [2] from rfl,
    applyWord_append,delayed_prefix20]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix33 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0] = (ofSix (-16) (1) (1) (-6) (-30) (2)) := by
  rw [show ([2,3,2,0] : List (Fin 4)) = [2,3,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix21]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix34 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2,3] = (ofSix (16) (-3) (1) (-18) (14) (-2)) := by
  rw [show ([2,3,2,3] : List (Fin 4)) = [2,3,2] ++ [3] from rfl,
    applyWord_append,delayed_prefix21]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix35 : applyWord (WitnessLStarData.delayed.node 0) [0,1,2,1,2] = (ofSix (-2) (1) (-2) (-2) (10) (-7)) := by
  rw [show ([0,1,2,1,2] : List (Fin 4)) = [0,1,2,1] ++ [2] from rfl,
    applyWord_append,delayed_prefix22]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix36 : applyWord (WitnessLStarData.delayed.node 0) [0,1,2,3,0] = (ofSix (8) (1) (-2) (2) (12) (3)) := by
  rw [show ([0,1,2,3,0] : List (Fin 4)) = [0,1,2,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix23]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix37 : applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2,0] = (ofSix (10) (-2) (-1) (18) (8) (1)) := by
  rw [show ([0,1,3,2,0] : List (Fin 4)) = [0,1,3,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix24]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix38 : applyWord (WitnessLStarData.delayed.node 0) [0,3,2,1,3] = (ofSix (0) (9) (-1) (10) (-2) (7)) := by
  rw [show ([0,3,2,1,3] : List (Fin 4)) = [0,3,2,1] ++ [3] from rfl,
    applyWord_append,delayed_prefix26]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix39 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2] = (ofSix (-64) (1) (1) (-58) (574) (-10)) := by
  rw [show ([2,0,1,3,2] : List (Fin 4)) = [2,0,1,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix28]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix40 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,0,3] = (ofSix (-2) (-10) (1) (-154) (14) (-11)) := by
  rw [show ([2,1,2,0,3] : List (Fin 4)) = [2,1,2,0] ++ [3] from rfl,
    applyWord_append,delayed_prefix29]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix41 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0] = (ofSix (-16) (1) (1) (-154) (-2) (-10)) := by
  rw [show ([2,1,2,3,0] : List (Fin 4)) = [2,1,2,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix30]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix42 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,2] = (ofSix (16) (1) (-11) (138) (-1366) (10)) := by
  rw [show ([2,1,2,3,2] : List (Fin 4)) = [2,1,2,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix30]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix43 : applyWord (WitnessLStarData.delayed.node 0) [2,1,3,0,2] = (ofSix (-638) (11) (-10) (-58) (-6) (1)) := by
  rw [show ([2,1,3,0,2] : List (Fin 4)) = [2,1,3,0] ++ [2] from rfl,
    applyWord_append,delayed_prefix31]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix44 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0,3] = (ofSix (14) (1) (-1) (-66) (30) (-2)) := by
  rw [show ([2,3,2,0,3] : List (Fin 4)) = [2,3,2,0] ++ [3] from rfl,
    applyWord_append,delayed_prefix33]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix45 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2,3,0] = (ofSix (-16) (3) (-1) (-66) (14) (1)) := by
  rw [show ([2,3,2,3,0] : List (Fin 4)) = [2,3,2,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix34]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix46 : applyWord (WitnessLStarData.delayed.node 0) [0,1,2,1,2,0] = (ofSix (2) (-1) (2) (0) (10) (-9)) := by
  rw [show ([0,1,2,1,2,0] : List (Fin 4)) = [0,1,2,1,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix35]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix47 : applyWord (WitnessLStarData.delayed.node 0) [0,1,2,3,0,2] = (ofSix (8) (-1) (1) (-2) (18) (-3)) := by
  rw [show ([0,1,2,3,0,2] : List (Fin 4)) = [0,1,2,3,0] ++ [2] from rfl,
    applyWord_append,delayed_prefix36]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix48 : applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2,0,2] = (ofSix (-26) (2) (-1) (-18) (26) (-1)) := by
  rw [show ([0,1,3,2,0,2] : List (Fin 4)) = [0,1,3,2,0] ++ [2] from rfl,
    applyWord_append,delayed_prefix37]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix49 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0] = (ofSix (64) (-1) (-1) (6) (638) (-10)) := by
  rw [show ([2,0,1,3,2,0] : List (Fin 4)) = [2,0,1,3,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix39]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix50 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,3] = (ofSix (-64) (11) (-1) (5682) (-574) (10)) := by
  rw [show ([2,0,1,3,2,3] : List (Fin 4)) = [2,0,1,3,2] ++ [3] from rfl,
    applyWord_append,delayed_prefix39]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix51 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0,2] = (ofSix (138) (-1) (1) (154) (-1542) (10)) := by
  rw [show ([2,1,2,3,0,2] : List (Fin 4)) = [2,1,2,3,0] ++ [2] from rfl,
    applyWord_append,delayed_prefix41]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix52 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,2,0] = (ofSix (-16) (-1) (11) (138) (-1542) (-1)) := by
  rw [show ([2,1,2,3,2,0] : List (Fin 4)) = [2,1,2,3,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix42]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix53 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0,3,2] = (ofSix (80) (-1) (-1) (66) (-102) (2)) := by
  rw [show ([2,3,2,0,3,2] : List (Fin 4)) = [2,3,2,0,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix44]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix54 : applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2,0,2,3] = (ofSix (-52) (2) (1) (8) (-26) (1)) := by
  rw [show ([0,1,3,2,0,2,3] : List (Fin 4)) = [0,1,3,2,0,2] ++ [3] from rfl,
    applyWord_append,delayed_prefix48]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix55 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0,3] = (ofSix (-574) (-1) (1) (6386) (-638) (10)) := by
  rw [show ([2,0,1,3,2,0,3] : List (Fin 4)) = [2,0,1,3,2,0] ++ [3] from rfl,
    applyWord_append,delayed_prefix49]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix56 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,3,0] = (ofSix (64) (-11) (1) (6386) (-574) (-1)) := by
  rw [show ([2,0,1,3,2,3,0] : List (Fin 4)) = [2,0,1,3,2,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix50]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix57 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0,2,3] = (ofSix (1680) (-1) (-1) (-15266) (1542) (-10)) := by
  rw [show ([2,1,2,3,0,2,3] : List (Fin 4)) = [2,1,2,3,0,2] ++ [3] from rfl,
    applyWord_append,delayed_prefix51]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix58 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0,3,2,0] = (ofSix (-80) (1) (1) (-14) (-182) (2)) := by
  rw [show ([2,3,2,0,3,2,0] : List (Fin 4)) = [2,3,2,0,3,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix53]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix59 : applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2,0,2,3,2] = (ofSix (-52) (-2) (3) (-8) (-18) (-1)) := by
  rw [show ([0,1,3,2,0,2,3,2] : List (Fin 4)) = [0,1,3,2,0,2,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix54]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix60 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0,3,2] = (ofSix (-6960) (1) (1) (-6386) (63222) (-10)) := by
  rw [show ([2,0,1,3,2,0,3,2] : List (Fin 4)) = [2,0,1,3,2,0,3] ++ [2] from rfl,
    applyWord_append,delayed_prefix55]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix61 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0,2,3,0] = (ofSix (-1680) (1) (1) (-16946) (-138) (-10)) := by
  rw [show ([2,1,2,3,0,2,3,0] : List (Fin 4)) = [2,1,2,3,0,2,3] ++ [0] from rfl,
    applyWord_append,delayed_prefix57]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix62 : applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0,3,2,0,2] = (ofSix (-66) (-1) (3) (14) (-182) (-2)) := by
  rw [show ([2,3,2,0,3,2,0,2] : List (Fin 4)) = [2,3,2,0,3,2,0] ++ [2] from rfl,
    applyWord_append,delayed_prefix58]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix63 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0,3,2,0] = (ofSix (6960) (-1) (-1) (574) (70182) (-10)) := by
  rw [show ([2,0,1,3,2,0,3,2,0] : List (Fin 4)) = [2,0,1,3,2,0,3,2] ++ [0] from rfl,
    applyWord_append,delayed_prefix60]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix64 : applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0,2,3,0,3] = (ofSix (-1542) (11) (-1) (-16946) (138) (10)) := by
  rw [show ([2,1,2,3,0,2,3,0,3] : List (Fin 4)) = [2,1,2,3,0,2,3,0] ++ [3] from rfl,
    applyWord_append,delayed_prefix61]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_prefix65 : applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0,3,2,0,2] = (ofSix (6386) (1) (-11) (-574) (70182) (10)) := by
  rw [show ([2,0,1,3,2,0,3,2,0,2] : List (Fin 4)) = [2,0,1,3,2,0,3,2,0] ++ [2] from rfl,
    applyWord_append,delayed_prefix63]
  apply entriesEqual_eq
  decide +kernel

private theorem delayed_reachable0 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 0).word) (WitnessLStarData.delayed.node 0) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) []) (ofSix (0) (-1) (3) (-2) (-2) (-2))
  rw [delayed_prefix0]
  intro u v; rfl

private theorem delayed_cyclic0 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 0) := by decide +kernel

private theorem delayed_edge0_0 :
    EdgeChecks WitnessLStarData.delayed 0 0 ((WitnessLStarData.delayed.core 0).edges 0) := by decide +kernel

private theorem delayed_edge0_1 :
    EdgeChecks WitnessLStarData.delayed 0 1 ((WitnessLStarData.delayed.core 0).edges 1) := by decide +kernel

private theorem delayed_edge0_2 :
    EdgeChecks WitnessLStarData.delayed 0 2 ((WitnessLStarData.delayed.core 0).edges 2) := by decide +kernel

private theorem delayed_edge0_3 :
    EdgeChecks WitnessLStarData.delayed 0 3 ((WitnessLStarData.delayed.core 0).edges 3) := by decide +kernel

private theorem delayed_triangles0 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 0) = true := by decide +kernel

private theorem delayed_descent0 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 0) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-1) (3) (-2) (-2) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable1 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 1).word) (WitnessLStarData.delayed.node 1) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0]) (ofSix (0) (1) (-3) (-2) (-2) (1))
  rw [delayed_prefix1]
  intro u v; rfl

private theorem delayed_cyclic1 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 1) := by decide +kernel

private theorem delayed_edge1_0 :
    EdgeChecks WitnessLStarData.delayed 1 0 ((WitnessLStarData.delayed.core 1).edges 0) := by decide +kernel

private theorem delayed_edge1_1 :
    EdgeChecks WitnessLStarData.delayed 1 1 ((WitnessLStarData.delayed.core 1).edges 1) := by decide +kernel

private theorem delayed_edge1_2 :
    EdgeChecks WitnessLStarData.delayed 1 2 ((WitnessLStarData.delayed.core 1).edges 2) := by decide +kernel

private theorem delayed_edge1_3 :
    EdgeChecks WitnessLStarData.delayed 1 3 ((WitnessLStarData.delayed.core 1).edges 3) := by decide +kernel

private theorem delayed_triangles1 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 1) = true := by decide +kernel

private theorem delayed_descent1 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 1) = true := by
  change allTriangleDescentsCheck (ofSix (0) (1) (-3) (-2) (-2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable2 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 2).word) (WitnessLStarData.delayed.node 2) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [1]) (ofSix (0) (-1) (3) (2) (2) (-2))
  rw [delayed_prefix2]
  intro u v; rfl

private theorem delayed_cyclic2 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 2) := by decide +kernel

private theorem delayed_edge2_0 :
    EdgeChecks WitnessLStarData.delayed 2 0 ((WitnessLStarData.delayed.core 2).edges 0) := by decide +kernel

private theorem delayed_edge2_1 :
    EdgeChecks WitnessLStarData.delayed 2 1 ((WitnessLStarData.delayed.core 2).edges 1) := by decide +kernel

private theorem delayed_edge2_2 :
    EdgeChecks WitnessLStarData.delayed 2 2 ((WitnessLStarData.delayed.core 2).edges 2) := by decide +kernel

private theorem delayed_edge2_3 :
    EdgeChecks WitnessLStarData.delayed 2 3 ((WitnessLStarData.delayed.core 2).edges 3) := by decide +kernel

private theorem delayed_triangles2 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 2) = true := by decide +kernel

private theorem delayed_descent2 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 2) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-1) (3) (2) (2) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable3 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 3).word) (WitnessLStarData.delayed.node 3) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2]) (ofSix (0) (1) (1) (2) (-6) (2))
  rw [delayed_prefix3]
  intro u v; rfl

private theorem delayed_cyclic3 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 3) := by decide +kernel

private theorem delayed_edge3_0 :
    EdgeChecks WitnessLStarData.delayed 3 0 ((WitnessLStarData.delayed.core 3).edges 0) := by decide +kernel

private theorem delayed_edge3_1 :
    EdgeChecks WitnessLStarData.delayed 3 1 ((WitnessLStarData.delayed.core 3).edges 1) := by decide +kernel

private theorem delayed_edge3_2 :
    EdgeChecks WitnessLStarData.delayed 3 2 ((WitnessLStarData.delayed.core 3).edges 2) := by decide +kernel

private theorem delayed_edge3_3 :
    EdgeChecks WitnessLStarData.delayed 3 3 ((WitnessLStarData.delayed.core 3).edges 3) := by decide +kernel

private theorem delayed_triangles3 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 3) = true := by decide +kernel

private theorem delayed_descent3 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 3) = true := by
  change allTriangleDescentsCheck (ofSix (0) (1) (1) (2) (-6) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable4 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 4).word) (WitnessLStarData.delayed.node 4) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1]) (ofSix (0) (1) (-3) (2) (2) (1))
  rw [delayed_prefix4]
  intro u v; rfl

private theorem delayed_cyclic4 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 4) := by decide +kernel

private theorem delayed_edge4_0 :
    EdgeChecks WitnessLStarData.delayed 4 0 ((WitnessLStarData.delayed.core 4).edges 0) := by decide +kernel

private theorem delayed_edge4_1 :
    EdgeChecks WitnessLStarData.delayed 4 1 ((WitnessLStarData.delayed.core 4).edges 1) := by decide +kernel

private theorem delayed_edge4_2 :
    EdgeChecks WitnessLStarData.delayed 4 2 ((WitnessLStarData.delayed.core 4).edges 2) := by decide +kernel

private theorem delayed_edge4_3 :
    EdgeChecks WitnessLStarData.delayed 4 3 ((WitnessLStarData.delayed.core 4).edges 3) := by decide +kernel

private theorem delayed_triangles4 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 4) = true := by decide +kernel

private theorem delayed_descent4 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 4) = true := by
  change allTriangleDescentsCheck (ofSix (0) (1) (-3) (2) (2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable5 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 5).word) (WitnessLStarData.delayed.node 5) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,2]) (ofSix (2) (-1) (-2) (2) (-2) (-1))
  rw [delayed_prefix5]
  intro u v; rfl

private theorem delayed_cyclic5 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 5) := by decide +kernel

private theorem delayed_edge5_0 :
    EdgeChecks WitnessLStarData.delayed 5 0 ((WitnessLStarData.delayed.core 5).edges 0) := by decide +kernel

private theorem delayed_edge5_1 :
    EdgeChecks WitnessLStarData.delayed 5 1 ((WitnessLStarData.delayed.core 5).edges 1) := by decide +kernel

private theorem delayed_edge5_2 :
    EdgeChecks WitnessLStarData.delayed 5 2 ((WitnessLStarData.delayed.core 5).edges 2) := by decide +kernel

private theorem delayed_edge5_3 :
    EdgeChecks WitnessLStarData.delayed 5 3 ((WitnessLStarData.delayed.core 5).edges 3) := by decide +kernel

private theorem delayed_triangles5 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 5) = true := by decide +kernel

private theorem delayed_descent5 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 5) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (-2) (2) (-2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable6 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 6).word) (WitnessLStarData.delayed.node 6) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,3]) (ofSix (0) (-2) (3) (-4) (2) (-1))
  rw [delayed_prefix6]
  intro u v; rfl

private theorem delayed_cyclic6 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 6) := by decide +kernel

private theorem delayed_edge6_0 :
    EdgeChecks WitnessLStarData.delayed 6 0 ((WitnessLStarData.delayed.core 6).edges 0) := by decide +kernel

private theorem delayed_edge6_1 :
    EdgeChecks WitnessLStarData.delayed 6 1 ((WitnessLStarData.delayed.core 6).edges 1) := by decide +kernel

private theorem delayed_edge6_2 :
    EdgeChecks WitnessLStarData.delayed 6 2 ((WitnessLStarData.delayed.core 6).edges 2) := by decide +kernel

private theorem delayed_edge6_3 :
    EdgeChecks WitnessLStarData.delayed 6 3 ((WitnessLStarData.delayed.core 6).edges 3) := by decide +kernel

private theorem delayed_triangles6 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 6) = true := by decide +kernel

private theorem delayed_descent6 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 6) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-2) (3) (-4) (2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable7 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 7).word) (WitnessLStarData.delayed.node 7) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [1,2]) (ofSix (-2) (1) (1) (-2) (2) (2))
  rw [delayed_prefix7]
  intro u v; rfl

private theorem delayed_cyclic7 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 7) := by decide +kernel

private theorem delayed_edge7_0 :
    EdgeChecks WitnessLStarData.delayed 7 0 ((WitnessLStarData.delayed.core 7).edges 0) := by decide +kernel

private theorem delayed_edge7_1 :
    EdgeChecks WitnessLStarData.delayed 7 1 ((WitnessLStarData.delayed.core 7).edges 1) := by decide +kernel

private theorem delayed_edge7_2 :
    EdgeChecks WitnessLStarData.delayed 7 2 ((WitnessLStarData.delayed.core 7).edges 2) := by decide +kernel

private theorem delayed_edge7_3 :
    EdgeChecks WitnessLStarData.delayed 7 3 ((WitnessLStarData.delayed.core 7).edges 3) := by decide +kernel

private theorem delayed_triangles7 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 7) = true := by decide +kernel

private theorem delayed_descent7 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 7) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (1) (1) (-2) (2) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable8 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 8).word) (WitnessLStarData.delayed.node 8) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0]) (ofSix (0) (-1) (-1) (2) (-6) (2))
  rw [delayed_prefix8]
  intro u v; rfl

private theorem delayed_cyclic8 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 8) := by decide +kernel

private theorem delayed_edge8_0 :
    EdgeChecks WitnessLStarData.delayed 8 0 ((WitnessLStarData.delayed.core 8).edges 0) := by decide +kernel

private theorem delayed_edge8_1 :
    EdgeChecks WitnessLStarData.delayed 8 1 ((WitnessLStarData.delayed.core 8).edges 1) := by decide +kernel

private theorem delayed_edge8_2 :
    EdgeChecks WitnessLStarData.delayed 8 2 ((WitnessLStarData.delayed.core 8).edges 2) := by decide +kernel

private theorem delayed_edge8_3 :
    EdgeChecks WitnessLStarData.delayed 8 3 ((WitnessLStarData.delayed.core 8).edges 3) := by decide +kernel

private theorem delayed_triangles8 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 8) = true := by decide +kernel

private theorem delayed_descent8 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 8) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-1) (-1) (2) (-6) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable9 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 9).word) (WitnessLStarData.delayed.node 9) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1]) (ofSix (0) (1) (1) (-2) (6) (-10))
  rw [delayed_prefix9]
  intro u v; rfl

private theorem delayed_cyclic9 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 9) := by decide +kernel

private theorem delayed_edge9_0 :
    EdgeChecks WitnessLStarData.delayed 9 0 ((WitnessLStarData.delayed.core 9).edges 0) := by decide +kernel

private theorem delayed_edge9_1 :
    EdgeChecks WitnessLStarData.delayed 9 1 ((WitnessLStarData.delayed.core 9).edges 1) := by decide +kernel

private theorem delayed_edge9_2 :
    EdgeChecks WitnessLStarData.delayed 9 2 ((WitnessLStarData.delayed.core 9).edges 2) := by decide +kernel

private theorem delayed_edge9_3 :
    EdgeChecks WitnessLStarData.delayed 9 3 ((WitnessLStarData.delayed.core 9).edges 3) := by decide +kernel

private theorem delayed_triangles9 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 9) = true := by decide +kernel

private theorem delayed_descent9 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 9) = true := by
  change allTriangleDescentsCheck (ofSix (0) (1) (1) (-2) (6) (-10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable10 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 10).word) (WitnessLStarData.delayed.node 10) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3]) (ofSix (6) (1) (-1) (-10) (6) (-2))
  rw [delayed_prefix10]
  intro u v; rfl

private theorem delayed_cyclic10 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 10) := by decide +kernel

private theorem delayed_edge10_0 :
    EdgeChecks WitnessLStarData.delayed 10 0 ((WitnessLStarData.delayed.core 10).edges 0) := by decide +kernel

private theorem delayed_edge10_1 :
    EdgeChecks WitnessLStarData.delayed 10 1 ((WitnessLStarData.delayed.core 10).edges 1) := by decide +kernel

private theorem delayed_edge10_2 :
    EdgeChecks WitnessLStarData.delayed 10 2 ((WitnessLStarData.delayed.core 10).edges 2) := by decide +kernel

private theorem delayed_edge10_3 :
    EdgeChecks WitnessLStarData.delayed 10 3 ((WitnessLStarData.delayed.core 10).edges 3) := by decide +kernel

private theorem delayed_triangles10 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 10) = true := by decide +kernel

private theorem delayed_descent10 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 10) = true := by
  change allTriangleDescentsCheck (ofSix (6) (1) (-1) (-10) (6) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable11 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 11).word) (WitnessLStarData.delayed.node 11) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,2]) (ofSix (0) (-1) (-2) (-2) (4) (-1))
  rw [delayed_prefix11]
  intro u v; rfl

private theorem delayed_cyclic11 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 11) := by decide +kernel

private theorem delayed_edge11_0 :
    EdgeChecks WitnessLStarData.delayed 11 0 ((WitnessLStarData.delayed.core 11).edges 0) := by decide +kernel

private theorem delayed_edge11_1 :
    EdgeChecks WitnessLStarData.delayed 11 1 ((WitnessLStarData.delayed.core 11).edges 1) := by decide +kernel

private theorem delayed_edge11_2 :
    EdgeChecks WitnessLStarData.delayed 11 2 ((WitnessLStarData.delayed.core 11).edges 2) := by decide +kernel

private theorem delayed_edge11_3 :
    EdgeChecks WitnessLStarData.delayed 11 3 ((WitnessLStarData.delayed.core 11).edges 3) := by decide +kernel

private theorem delayed_triangles11 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 11) = true := by decide +kernel

private theorem delayed_descent11 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 11) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-1) (-2) (-2) (4) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable12 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 12).word) (WitnessLStarData.delayed.node 12) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,3]) (ofSix (-6) (-2) (3) (2) (-2) (-1))
  rw [delayed_prefix12]
  intro u v; rfl

private theorem delayed_cyclic12 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 12) := by decide +kernel

private theorem delayed_edge12_0 :
    EdgeChecks WitnessLStarData.delayed 12 0 ((WitnessLStarData.delayed.core 12).edges 0) := by decide +kernel

private theorem delayed_edge12_1 :
    EdgeChecks WitnessLStarData.delayed 12 1 ((WitnessLStarData.delayed.core 12).edges 1) := by decide +kernel

private theorem delayed_edge12_2 :
    EdgeChecks WitnessLStarData.delayed 12 2 ((WitnessLStarData.delayed.core 12).edges 2) := by decide +kernel

private theorem delayed_edge12_3 :
    EdgeChecks WitnessLStarData.delayed 12 3 ((WitnessLStarData.delayed.core 12).edges 3) := by decide +kernel

private theorem delayed_triangles12 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 12) = true := by decide +kernel

private theorem delayed_descent12 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 12) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (-2) (3) (2) (-2) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable13 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 13).word) (WitnessLStarData.delayed.node 13) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,3,0]) (ofSix (0) (2) (-3) (-4) (2) (5))
  rw [delayed_prefix13]
  intro u v; rfl

private theorem delayed_cyclic13 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 13) := by decide +kernel

private theorem delayed_edge13_0 :
    EdgeChecks WitnessLStarData.delayed 13 0 ((WitnessLStarData.delayed.core 13).edges 0) := by decide +kernel

private theorem delayed_edge13_1 :
    EdgeChecks WitnessLStarData.delayed 13 1 ((WitnessLStarData.delayed.core 13).edges 1) := by decide +kernel

private theorem delayed_edge13_2 :
    EdgeChecks WitnessLStarData.delayed 13 2 ((WitnessLStarData.delayed.core 13).edges 2) := by decide +kernel

private theorem delayed_edge13_3 :
    EdgeChecks WitnessLStarData.delayed 13 3 ((WitnessLStarData.delayed.core 13).edges 3) := by decide +kernel

private theorem delayed_triangles13 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 13) = true := by decide +kernel

private theorem delayed_descent13 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 13) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (-3) (-4) (2) (5)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable14 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 14).word) (WitnessLStarData.delayed.node 14) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,3,1]) (ofSix (0) (-2) (3) (4) (-2) (7))
  rw [delayed_prefix14]
  intro u v; rfl

private theorem delayed_cyclic14 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 14) := by decide +kernel

private theorem delayed_edge14_0 :
    EdgeChecks WitnessLStarData.delayed 14 0 ((WitnessLStarData.delayed.core 14).edges 0) := by decide +kernel

private theorem delayed_edge14_1 :
    EdgeChecks WitnessLStarData.delayed 14 1 ((WitnessLStarData.delayed.core 14).edges 1) := by decide +kernel

private theorem delayed_edge14_2 :
    EdgeChecks WitnessLStarData.delayed 14 2 ((WitnessLStarData.delayed.core 14).edges 2) := by decide +kernel

private theorem delayed_edge14_3 :
    EdgeChecks WitnessLStarData.delayed 14 3 ((WitnessLStarData.delayed.core 14).edges 3) := by decide +kernel

private theorem delayed_triangles14 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 14) = true := by decide +kernel

private theorem delayed_descent14 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 14) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-2) (3) (4) (-2) (7)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable15 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 15).word) (WitnessLStarData.delayed.node 15) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,3,2]) (ofSix (0) (2) (1) (4) (-2) (1))
  rw [delayed_prefix15]
  intro u v; rfl

private theorem delayed_cyclic15 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 15) := by decide +kernel

private theorem delayed_edge15_0 :
    EdgeChecks WitnessLStarData.delayed 15 0 ((WitnessLStarData.delayed.core 15).edges 0) := by decide +kernel

private theorem delayed_edge15_1 :
    EdgeChecks WitnessLStarData.delayed 15 1 ((WitnessLStarData.delayed.core 15).edges 1) := by decide +kernel

private theorem delayed_edge15_2 :
    EdgeChecks WitnessLStarData.delayed 15 2 ((WitnessLStarData.delayed.core 15).edges 2) := by decide +kernel

private theorem delayed_edge15_3 :
    EdgeChecks WitnessLStarData.delayed 15 3 ((WitnessLStarData.delayed.core 15).edges 3) := by decide +kernel

private theorem delayed_triangles15 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 15) = true := by decide +kernel

private theorem delayed_descent15 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 15) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (1) (4) (-2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable16 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 16).word) (WitnessLStarData.delayed.node 16) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1]) (ofSix (0) (-1) (-1) (-2) (6) (-10))
  rw [delayed_prefix16]
  intro u v; rfl

private theorem delayed_cyclic16 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 16) := by decide +kernel

private theorem delayed_edge16_0 :
    EdgeChecks WitnessLStarData.delayed 16 0 ((WitnessLStarData.delayed.core 16).edges 0) := by decide +kernel

private theorem delayed_edge16_1 :
    EdgeChecks WitnessLStarData.delayed 16 1 ((WitnessLStarData.delayed.core 16).edges 1) := by decide +kernel

private theorem delayed_edge16_2 :
    EdgeChecks WitnessLStarData.delayed 16 2 ((WitnessLStarData.delayed.core 16).edges 2) := by decide +kernel

private theorem delayed_edge16_3 :
    EdgeChecks WitnessLStarData.delayed 16 3 ((WitnessLStarData.delayed.core 16).edges 3) := by decide +kernel

private theorem delayed_triangles16 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 16) = true := by decide +kernel

private theorem delayed_descent16 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 16) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-1) (-1) (-2) (6) (-10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable17 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 17).word) (WitnessLStarData.delayed.node 17) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,3]) (ofSix (0) (-3) (1) (-10) (6) (-2))
  rw [delayed_prefix17]
  intro u v; rfl

private theorem delayed_cyclic17 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 17) := by decide +kernel

private theorem delayed_edge17_0 :
    EdgeChecks WitnessLStarData.delayed 17 0 ((WitnessLStarData.delayed.core 17).edges 0) := by decide +kernel

private theorem delayed_edge17_1 :
    EdgeChecks WitnessLStarData.delayed 17 1 ((WitnessLStarData.delayed.core 17).edges 1) := by decide +kernel

private theorem delayed_edge17_2 :
    EdgeChecks WitnessLStarData.delayed 17 2 ((WitnessLStarData.delayed.core 17).edges 2) := by decide +kernel

private theorem delayed_edge17_3 :
    EdgeChecks WitnessLStarData.delayed 17 3 ((WitnessLStarData.delayed.core 17).edges 3) := by decide +kernel

private theorem delayed_triangles17 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 17) = true := by decide +kernel

private theorem delayed_descent17 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 17) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-3) (1) (-10) (6) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable18 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 18).word) (WitnessLStarData.delayed.node 18) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2]) (ofSix (2) (-1) (1) (2) (-14) (10))
  rw [delayed_prefix18]
  intro u v; rfl

private theorem delayed_cyclic18 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 18) := by decide +kernel

private theorem delayed_edge18_0 :
    EdgeChecks WitnessLStarData.delayed 18 0 ((WitnessLStarData.delayed.core 18).edges 0) := by decide +kernel

private theorem delayed_edge18_1 :
    EdgeChecks WitnessLStarData.delayed 18 1 ((WitnessLStarData.delayed.core 18).edges 1) := by decide +kernel

private theorem delayed_edge18_2 :
    EdgeChecks WitnessLStarData.delayed 18 2 ((WitnessLStarData.delayed.core 18).edges 2) := by decide +kernel

private theorem delayed_edge18_3 :
    EdgeChecks WitnessLStarData.delayed 18 3 ((WitnessLStarData.delayed.core 18).edges 3) := by decide +kernel

private theorem delayed_triangles18 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 18) = true := by decide +kernel

private theorem delayed_descent18 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 18) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (1) (2) (-14) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable19 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 19).word) (WitnessLStarData.delayed.node 19) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,3]) (ofSix (0) (11) (-1) (58) (-6) (10))
  rw [delayed_prefix19]
  intro u v; rfl

private theorem delayed_cyclic19 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 19) := by decide +kernel

private theorem delayed_edge19_0 :
    EdgeChecks WitnessLStarData.delayed 19 0 ((WitnessLStarData.delayed.core 19).edges 0) := by decide +kernel

private theorem delayed_edge19_1 :
    EdgeChecks WitnessLStarData.delayed 19 1 ((WitnessLStarData.delayed.core 19).edges 1) := by decide +kernel

private theorem delayed_edge19_2 :
    EdgeChecks WitnessLStarData.delayed 19 2 ((WitnessLStarData.delayed.core 19).edges 2) := by decide +kernel

private theorem delayed_edge19_3 :
    EdgeChecks WitnessLStarData.delayed 19 3 ((WitnessLStarData.delayed.core 19).edges 3) := by decide +kernel

private theorem delayed_triangles19 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 19) = true := by decide +kernel

private theorem delayed_descent19 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 19) = true := by
  change allTriangleDescentsCheck (ofSix (0) (11) (-1) (58) (-6) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable20 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 20).word) (WitnessLStarData.delayed.node 20) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,0]) (ofSix (-6) (-1) (1) (-10) (0) (-3))
  rw [delayed_prefix20]
  intro u v; rfl

private theorem delayed_cyclic20 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 20) := by decide +kernel

private theorem delayed_edge20_0 :
    EdgeChecks WitnessLStarData.delayed 20 0 ((WitnessLStarData.delayed.core 20).edges 0) := by decide +kernel

private theorem delayed_edge20_1 :
    EdgeChecks WitnessLStarData.delayed 20 1 ((WitnessLStarData.delayed.core 20).edges 1) := by decide +kernel

private theorem delayed_edge20_2 :
    EdgeChecks WitnessLStarData.delayed 20 2 ((WitnessLStarData.delayed.core 20).edges 2) := by decide +kernel

private theorem delayed_edge20_3 :
    EdgeChecks WitnessLStarData.delayed 20 3 ((WitnessLStarData.delayed.core 20).edges 3) := by decide +kernel

private theorem delayed_triangles20 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 20) = true := by decide +kernel

private theorem delayed_descent20 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 20) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (-1) (1) (-10) (0) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable21 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 21).word) (WitnessLStarData.delayed.node 21) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,2]) (ofSix (16) (-1) (-1) (10) (-14) (2))
  rw [delayed_prefix21]
  intro u v; rfl

private theorem delayed_cyclic21 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 21) := by decide +kernel

private theorem delayed_edge21_0 :
    EdgeChecks WitnessLStarData.delayed 21 0 ((WitnessLStarData.delayed.core 21).edges 0) := by decide +kernel

private theorem delayed_edge21_1 :
    EdgeChecks WitnessLStarData.delayed 21 1 ((WitnessLStarData.delayed.core 21).edges 1) := by decide +kernel

private theorem delayed_edge21_2 :
    EdgeChecks WitnessLStarData.delayed 21 2 ((WitnessLStarData.delayed.core 21).edges 2) := by decide +kernel

private theorem delayed_edge21_3 :
    EdgeChecks WitnessLStarData.delayed 21 3 ((WitnessLStarData.delayed.core 21).edges 3) := by decide +kernel

private theorem delayed_triangles21 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 21) = true := by decide +kernel

private theorem delayed_descent21 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 21) = true := by
  change allTriangleDescentsCheck (ofSix (16) (-1) (-1) (10) (-14) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable22 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 22).word) (WitnessLStarData.delayed.node 22) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,2,1]) (ofSix (0) (-1) (-2) (2) (-4) (7))
  rw [delayed_prefix22]
  intro u v; rfl

private theorem delayed_cyclic22 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 22) := by decide +kernel

private theorem delayed_edge22_0 :
    EdgeChecks WitnessLStarData.delayed 22 0 ((WitnessLStarData.delayed.core 22).edges 0) := by decide +kernel

private theorem delayed_edge22_1 :
    EdgeChecks WitnessLStarData.delayed 22 1 ((WitnessLStarData.delayed.core 22).edges 1) := by decide +kernel

private theorem delayed_edge22_2 :
    EdgeChecks WitnessLStarData.delayed 22 2 ((WitnessLStarData.delayed.core 22).edges 2) := by decide +kernel

private theorem delayed_edge22_3 :
    EdgeChecks WitnessLStarData.delayed 22 3 ((WitnessLStarData.delayed.core 22).edges 3) := by decide +kernel

private theorem delayed_triangles22 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 22) = true := by decide +kernel

private theorem delayed_descent22 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 22) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-1) (-2) (2) (-4) (7)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable23 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 23).word) (WitnessLStarData.delayed.node 23) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,2,3]) (ofSix (-8) (-1) (2) (2) (-4) (1))
  rw [delayed_prefix23]
  intro u v; rfl

private theorem delayed_cyclic23 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 23) := by decide +kernel

private theorem delayed_edge23_0 :
    EdgeChecks WitnessLStarData.delayed 23 0 ((WitnessLStarData.delayed.core 23).edges 0) := by decide +kernel

private theorem delayed_edge23_1 :
    EdgeChecks WitnessLStarData.delayed 23 1 ((WitnessLStarData.delayed.core 23).edges 1) := by decide +kernel

private theorem delayed_edge23_2 :
    EdgeChecks WitnessLStarData.delayed 23 2 ((WitnessLStarData.delayed.core 23).edges 2) := by decide +kernel

private theorem delayed_edge23_3 :
    EdgeChecks WitnessLStarData.delayed 23 3 ((WitnessLStarData.delayed.core 23).edges 3) := by decide +kernel

private theorem delayed_triangles23 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 23) = true := by decide +kernel

private theorem delayed_descent23 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 23) = true := by
  change allTriangleDescentsCheck (ofSix (-8) (-1) (2) (2) (-4) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable24 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 24).word) (WitnessLStarData.delayed.node 24) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2]) (ofSix (-10) (2) (1) (-2) (-2) (1))
  rw [delayed_prefix24]
  intro u v; rfl

private theorem delayed_cyclic24 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 24) := by decide +kernel

private theorem delayed_edge24_0 :
    EdgeChecks WitnessLStarData.delayed 24 0 ((WitnessLStarData.delayed.core 24).edges 0) := by decide +kernel

private theorem delayed_edge24_1 :
    EdgeChecks WitnessLStarData.delayed 24 1 ((WitnessLStarData.delayed.core 24).edges 1) := by decide +kernel

private theorem delayed_edge24_2 :
    EdgeChecks WitnessLStarData.delayed 24 2 ((WitnessLStarData.delayed.core 24).edges 2) := by decide +kernel

private theorem delayed_edge24_3 :
    EdgeChecks WitnessLStarData.delayed 24 3 ((WitnessLStarData.delayed.core 24).edges 3) := by decide +kernel

private theorem delayed_triangles24 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 24) = true := by decide +kernel

private theorem delayed_descent24 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 24) = true := by
  change allTriangleDescentsCheck (ofSix (-10) (2) (1) (-2) (-2) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable25 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 25).word) (WitnessLStarData.delayed.node 25) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,3,0,1]) (ofSix (0) (2) (-3) (4) (-2) (13))
  rw [delayed_prefix25]
  intro u v; rfl

private theorem delayed_cyclic25 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 25) := by decide +kernel

private theorem delayed_edge25_0 :
    EdgeChecks WitnessLStarData.delayed 25 0 ((WitnessLStarData.delayed.core 25).edges 0) := by decide +kernel

private theorem delayed_edge25_1 :
    EdgeChecks WitnessLStarData.delayed 25 1 ((WitnessLStarData.delayed.core 25).edges 1) := by decide +kernel

private theorem delayed_edge25_2 :
    EdgeChecks WitnessLStarData.delayed 25 2 ((WitnessLStarData.delayed.core 25).edges 2) := by decide +kernel

private theorem delayed_edge25_3 :
    EdgeChecks WitnessLStarData.delayed 25 3 ((WitnessLStarData.delayed.core 25).edges 3) := by decide +kernel

private theorem delayed_triangles25 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 25) = true := by decide +kernel

private theorem delayed_descent25 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 25) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (-3) (4) (-2) (13)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable26 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 26).word) (WitnessLStarData.delayed.node 26) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,3,2,1]) (ofSix (0) (2) (1) (-4) (2) (-7))
  rw [delayed_prefix26]
  intro u v; rfl

private theorem delayed_cyclic26 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 26) := by decide +kernel

private theorem delayed_edge26_0 :
    EdgeChecks WitnessLStarData.delayed 26 0 ((WitnessLStarData.delayed.core 26).edges 0) := by decide +kernel

private theorem delayed_edge26_1 :
    EdgeChecks WitnessLStarData.delayed 26 1 ((WitnessLStarData.delayed.core 26).edges 1) := by decide +kernel

private theorem delayed_edge26_2 :
    EdgeChecks WitnessLStarData.delayed 26 2 ((WitnessLStarData.delayed.core 26).edges 2) := by decide +kernel

private theorem delayed_edge26_3 :
    EdgeChecks WitnessLStarData.delayed 26 3 ((WitnessLStarData.delayed.core 26).edges 3) := by decide +kernel

private theorem delayed_triangles26 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 26) = true := by decide +kernel

private theorem delayed_descent26 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 26) = true := by
  change allTriangleDescentsCheck (ofSix (0) (2) (1) (-4) (2) (-7)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable27 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 27).word) (WitnessLStarData.delayed.node 27) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,2]) (ofSix (0) (1) (-11) (2) (-14) (10))
  rw [delayed_prefix27]
  intro u v; rfl

private theorem delayed_cyclic27 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 27) := by decide +kernel

private theorem delayed_edge27_0 :
    EdgeChecks WitnessLStarData.delayed 27 0 ((WitnessLStarData.delayed.core 27).edges 0) := by decide +kernel

private theorem delayed_edge27_1 :
    EdgeChecks WitnessLStarData.delayed 27 1 ((WitnessLStarData.delayed.core 27).edges 1) := by decide +kernel

private theorem delayed_edge27_2 :
    EdgeChecks WitnessLStarData.delayed 27 2 ((WitnessLStarData.delayed.core 27).edges 2) := by decide +kernel

private theorem delayed_edge27_3 :
    EdgeChecks WitnessLStarData.delayed 27 3 ((WitnessLStarData.delayed.core 27).edges 3) := by decide +kernel

private theorem delayed_triangles27 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 27) = true := by decide +kernel

private theorem delayed_descent27 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 27) = true := by
  change allTriangleDescentsCheck (ofSix (0) (1) (-11) (2) (-14) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable28 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 28).word) (WitnessLStarData.delayed.node 28) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3]) (ofSix (-6) (-1) (1) (58) (-6) (10))
  rw [delayed_prefix28]
  intro u v; rfl

private theorem delayed_cyclic28 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 28) := by decide +kernel

private theorem delayed_edge28_0 :
    EdgeChecks WitnessLStarData.delayed 28 0 ((WitnessLStarData.delayed.core 28).edges 0) := by decide +kernel

private theorem delayed_edge28_1 :
    EdgeChecks WitnessLStarData.delayed 28 1 ((WitnessLStarData.delayed.core 28).edges 1) := by decide +kernel

private theorem delayed_edge28_2 :
    EdgeChecks WitnessLStarData.delayed 28 2 ((WitnessLStarData.delayed.core 28).edges 2) := by decide +kernel

private theorem delayed_edge28_3 :
    EdgeChecks WitnessLStarData.delayed 28 3 ((WitnessLStarData.delayed.core 28).edges 3) := by decide +kernel

private theorem delayed_triangles28 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 28) = true := by decide +kernel

private theorem delayed_descent28 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 28) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (-1) (1) (58) (-6) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable29 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 29).word) (WitnessLStarData.delayed.node 29) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,0]) (ofSix (-2) (1) (-1) (0) (-14) (11))
  rw [delayed_prefix29]
  intro u v; rfl

private theorem delayed_cyclic29 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 29) := by decide +kernel

private theorem delayed_edge29_0 :
    EdgeChecks WitnessLStarData.delayed 29 0 ((WitnessLStarData.delayed.core 29).edges 0) := by decide +kernel

private theorem delayed_edge29_1 :
    EdgeChecks WitnessLStarData.delayed 29 1 ((WitnessLStarData.delayed.core 29).edges 1) := by decide +kernel

private theorem delayed_edge29_2 :
    EdgeChecks WitnessLStarData.delayed 29 2 ((WitnessLStarData.delayed.core 29).edges 2) := by decide +kernel

private theorem delayed_edge29_3 :
    EdgeChecks WitnessLStarData.delayed 29 3 ((WitnessLStarData.delayed.core 29).edges 3) := by decide +kernel

private theorem delayed_triangles29 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 29) = true := by decide +kernel

private theorem delayed_descent29 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 29) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (1) (-1) (0) (-14) (11)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable30 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 30).word) (WitnessLStarData.delayed.node 30) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3]) (ofSix (16) (-1) (-1) (-138) (14) (-10))
  rw [delayed_prefix30]
  intro u v; rfl

private theorem delayed_cyclic30 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 30) := by decide +kernel

private theorem delayed_edge30_0 :
    EdgeChecks WitnessLStarData.delayed 30 0 ((WitnessLStarData.delayed.core 30).edges 0) := by decide +kernel

private theorem delayed_edge30_1 :
    EdgeChecks WitnessLStarData.delayed 30 1 ((WitnessLStarData.delayed.core 30).edges 1) := by decide +kernel

private theorem delayed_edge30_2 :
    EdgeChecks WitnessLStarData.delayed 30 2 ((WitnessLStarData.delayed.core 30).edges 2) := by decide +kernel

private theorem delayed_edge30_3 :
    EdgeChecks WitnessLStarData.delayed 30 3 ((WitnessLStarData.delayed.core 30).edges 3) := by decide +kernel

private theorem delayed_triangles30 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 30) = true := by decide +kernel

private theorem delayed_descent30 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 30) = true := by
  change allTriangleDescentsCheck (ofSix (16) (-1) (-1) (-138) (14) (-10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable31 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 31).word) (WitnessLStarData.delayed.node 31) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,3,0]) (ofSix (0) (-11) (1) (58) (-6) (-1))
  rw [delayed_prefix31]
  intro u v; rfl

private theorem delayed_cyclic31 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 31) := by decide +kernel

private theorem delayed_edge31_0 :
    EdgeChecks WitnessLStarData.delayed 31 0 ((WitnessLStarData.delayed.core 31).edges 0) := by decide +kernel

private theorem delayed_edge31_1 :
    EdgeChecks WitnessLStarData.delayed 31 1 ((WitnessLStarData.delayed.core 31).edges 1) := by decide +kernel

private theorem delayed_edge31_2 :
    EdgeChecks WitnessLStarData.delayed 31 2 ((WitnessLStarData.delayed.core 31).edges 2) := by decide +kernel

private theorem delayed_edge31_3 :
    EdgeChecks WitnessLStarData.delayed 31 3 ((WitnessLStarData.delayed.core 31).edges 3) := by decide +kernel

private theorem delayed_triangles31 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 31) = true := by decide +kernel

private theorem delayed_descent31 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 31) = true := by
  change allTriangleDescentsCheck (ofSix (0) (-11) (1) (58) (-6) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable32 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 32).word) (WitnessLStarData.delayed.node 32) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,0,2]) (ofSix (-6) (1) (-2) (10) (-30) (3))
  rw [delayed_prefix32]
  intro u v; rfl

private theorem delayed_cyclic32 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 32) := by decide +kernel

private theorem delayed_edge32_0 :
    EdgeChecks WitnessLStarData.delayed 32 0 ((WitnessLStarData.delayed.core 32).edges 0) := by decide +kernel

private theorem delayed_edge32_1 :
    EdgeChecks WitnessLStarData.delayed 32 1 ((WitnessLStarData.delayed.core 32).edges 1) := by decide +kernel

private theorem delayed_edge32_2 :
    EdgeChecks WitnessLStarData.delayed 32 2 ((WitnessLStarData.delayed.core 32).edges 2) := by decide +kernel

private theorem delayed_edge32_3 :
    EdgeChecks WitnessLStarData.delayed 32 3 ((WitnessLStarData.delayed.core 32).edges 3) := by decide +kernel

private theorem delayed_triangles32 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 32) = true := by decide +kernel

private theorem delayed_descent32 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 32) = true := by
  change allTriangleDescentsCheck (ofSix (-6) (1) (-2) (10) (-30) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable33 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 33).word) (WitnessLStarData.delayed.node 33) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0]) (ofSix (-16) (1) (1) (-6) (-30) (2))
  rw [delayed_prefix33]
  intro u v; rfl

private theorem delayed_cyclic33 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 33) := by decide +kernel

private theorem delayed_edge33_0 :
    EdgeChecks WitnessLStarData.delayed 33 0 ((WitnessLStarData.delayed.core 33).edges 0) := by decide +kernel

private theorem delayed_edge33_1 :
    EdgeChecks WitnessLStarData.delayed 33 1 ((WitnessLStarData.delayed.core 33).edges 1) := by decide +kernel

private theorem delayed_edge33_2 :
    EdgeChecks WitnessLStarData.delayed 33 2 ((WitnessLStarData.delayed.core 33).edges 2) := by decide +kernel

private theorem delayed_edge33_3 :
    EdgeChecks WitnessLStarData.delayed 33 3 ((WitnessLStarData.delayed.core 33).edges 3) := by decide +kernel

private theorem delayed_triangles33 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 33) = true := by decide +kernel

private theorem delayed_descent33 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 33) = true := by
  change allTriangleDescentsCheck (ofSix (-16) (1) (1) (-6) (-30) (2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable34 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 34).word) (WitnessLStarData.delayed.node 34) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,2,3]) (ofSix (16) (-3) (1) (-18) (14) (-2))
  rw [delayed_prefix34]
  intro u v; rfl

private theorem delayed_cyclic34 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 34) := by decide +kernel

private theorem delayed_edge34_0 :
    EdgeChecks WitnessLStarData.delayed 34 0 ((WitnessLStarData.delayed.core 34).edges 0) := by decide +kernel

private theorem delayed_edge34_1 :
    EdgeChecks WitnessLStarData.delayed 34 1 ((WitnessLStarData.delayed.core 34).edges 1) := by decide +kernel

private theorem delayed_edge34_2 :
    EdgeChecks WitnessLStarData.delayed 34 2 ((WitnessLStarData.delayed.core 34).edges 2) := by decide +kernel

private theorem delayed_edge34_3 :
    EdgeChecks WitnessLStarData.delayed 34 3 ((WitnessLStarData.delayed.core 34).edges 3) := by decide +kernel

private theorem delayed_triangles34 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 34) = true := by decide +kernel

private theorem delayed_descent34 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 34) = true := by
  change allTriangleDescentsCheck (ofSix (16) (-3) (1) (-18) (14) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable35 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 35).word) (WitnessLStarData.delayed.node 35) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,2,1,2]) (ofSix (-2) (1) (-2) (-2) (10) (-7))
  rw [delayed_prefix35]
  intro u v; rfl

private theorem delayed_cyclic35 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 35) := by decide +kernel

private theorem delayed_edge35_0 :
    EdgeChecks WitnessLStarData.delayed 35 0 ((WitnessLStarData.delayed.core 35).edges 0) := by decide +kernel

private theorem delayed_edge35_1 :
    EdgeChecks WitnessLStarData.delayed 35 1 ((WitnessLStarData.delayed.core 35).edges 1) := by decide +kernel

private theorem delayed_edge35_2 :
    EdgeChecks WitnessLStarData.delayed 35 2 ((WitnessLStarData.delayed.core 35).edges 2) := by decide +kernel

private theorem delayed_edge35_3 :
    EdgeChecks WitnessLStarData.delayed 35 3 ((WitnessLStarData.delayed.core 35).edges 3) := by decide +kernel

private theorem delayed_triangles35 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 35) = true := by decide +kernel

private theorem delayed_descent35 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 35) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (1) (-2) (-2) (10) (-7)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable36 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 36).word) (WitnessLStarData.delayed.node 36) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,2,3,0]) (ofSix (8) (1) (-2) (2) (12) (3))
  rw [delayed_prefix36]
  intro u v; rfl

private theorem delayed_cyclic36 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 36) := by decide +kernel

private theorem delayed_edge36_0 :
    EdgeChecks WitnessLStarData.delayed 36 0 ((WitnessLStarData.delayed.core 36).edges 0) := by decide +kernel

private theorem delayed_edge36_1 :
    EdgeChecks WitnessLStarData.delayed 36 1 ((WitnessLStarData.delayed.core 36).edges 1) := by decide +kernel

private theorem delayed_edge36_2 :
    EdgeChecks WitnessLStarData.delayed 36 2 ((WitnessLStarData.delayed.core 36).edges 2) := by decide +kernel

private theorem delayed_edge36_3 :
    EdgeChecks WitnessLStarData.delayed 36 3 ((WitnessLStarData.delayed.core 36).edges 3) := by decide +kernel

private theorem delayed_triangles36 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 36) = true := by decide +kernel

private theorem delayed_descent36 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 36) = true := by
  change allTriangleDescentsCheck (ofSix (8) (1) (-2) (2) (12) (3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable37 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 37).word) (WitnessLStarData.delayed.node 37) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2,0]) (ofSix (10) (-2) (-1) (18) (8) (1))
  rw [delayed_prefix37]
  intro u v; rfl

private theorem delayed_cyclic37 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 37) := by decide +kernel

private theorem delayed_edge37_0 :
    EdgeChecks WitnessLStarData.delayed 37 0 ((WitnessLStarData.delayed.core 37).edges 0) := by decide +kernel

private theorem delayed_edge37_1 :
    EdgeChecks WitnessLStarData.delayed 37 1 ((WitnessLStarData.delayed.core 37).edges 1) := by decide +kernel

private theorem delayed_edge37_2 :
    EdgeChecks WitnessLStarData.delayed 37 2 ((WitnessLStarData.delayed.core 37).edges 2) := by decide +kernel

private theorem delayed_edge37_3 :
    EdgeChecks WitnessLStarData.delayed 37 3 ((WitnessLStarData.delayed.core 37).edges 3) := by decide +kernel

private theorem delayed_triangles37 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 37) = true := by decide +kernel

private theorem delayed_descent37 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 37) = true := by
  change allTriangleDescentsCheck (ofSix (10) (-2) (-1) (18) (8) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable38 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 38).word) (WitnessLStarData.delayed.node 38) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,3,2,1,3]) (ofSix (0) (9) (-1) (10) (-2) (7))
  rw [delayed_prefix38]
  intro u v; rfl

private theorem delayed_cyclic38 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 38) := by decide +kernel

private theorem delayed_edge38_0 :
    EdgeChecks WitnessLStarData.delayed 38 0 ((WitnessLStarData.delayed.core 38).edges 0) := by decide +kernel

private theorem delayed_edge38_1 :
    EdgeChecks WitnessLStarData.delayed 38 1 ((WitnessLStarData.delayed.core 38).edges 1) := by decide +kernel

private theorem delayed_edge38_2 :
    EdgeChecks WitnessLStarData.delayed 38 2 ((WitnessLStarData.delayed.core 38).edges 2) := by decide +kernel

private theorem delayed_edge38_3 :
    EdgeChecks WitnessLStarData.delayed 38 3 ((WitnessLStarData.delayed.core 38).edges 3) := by decide +kernel

private theorem delayed_triangles38 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 38) = true := by decide +kernel

private theorem delayed_descent38 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 38) = true := by
  change allTriangleDescentsCheck (ofSix (0) (9) (-1) (10) (-2) (7)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable39 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 39).word) (WitnessLStarData.delayed.node 39) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2]) (ofSix (-64) (1) (1) (-58) (574) (-10))
  rw [delayed_prefix39]
  intro u v; rfl

private theorem delayed_cyclic39 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 39) := by decide +kernel

private theorem delayed_edge39_0 :
    EdgeChecks WitnessLStarData.delayed 39 0 ((WitnessLStarData.delayed.core 39).edges 0) := by decide +kernel

private theorem delayed_edge39_1 :
    EdgeChecks WitnessLStarData.delayed 39 1 ((WitnessLStarData.delayed.core 39).edges 1) := by decide +kernel

private theorem delayed_edge39_2 :
    EdgeChecks WitnessLStarData.delayed 39 2 ((WitnessLStarData.delayed.core 39).edges 2) := by decide +kernel

private theorem delayed_edge39_3 :
    EdgeChecks WitnessLStarData.delayed 39 3 ((WitnessLStarData.delayed.core 39).edges 3) := by decide +kernel

private theorem delayed_triangles39 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 39) = true := by decide +kernel

private theorem delayed_descent39 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 39) = true := by
  change allTriangleDescentsCheck (ofSix (-64) (1) (1) (-58) (574) (-10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable40 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 40).word) (WitnessLStarData.delayed.node 40) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,0,3]) (ofSix (-2) (-10) (1) (-154) (14) (-11))
  rw [delayed_prefix40]
  intro u v; rfl

private theorem delayed_cyclic40 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 40) := by decide +kernel

private theorem delayed_edge40_0 :
    EdgeChecks WitnessLStarData.delayed 40 0 ((WitnessLStarData.delayed.core 40).edges 0) := by decide +kernel

private theorem delayed_edge40_1 :
    EdgeChecks WitnessLStarData.delayed 40 1 ((WitnessLStarData.delayed.core 40).edges 1) := by decide +kernel

private theorem delayed_edge40_2 :
    EdgeChecks WitnessLStarData.delayed 40 2 ((WitnessLStarData.delayed.core 40).edges 2) := by decide +kernel

private theorem delayed_edge40_3 :
    EdgeChecks WitnessLStarData.delayed 40 3 ((WitnessLStarData.delayed.core 40).edges 3) := by decide +kernel

private theorem delayed_triangles40 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 40) = true := by decide +kernel

private theorem delayed_descent40 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 40) = true := by
  change allTriangleDescentsCheck (ofSix (-2) (-10) (1) (-154) (14) (-11)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable41 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 41).word) (WitnessLStarData.delayed.node 41) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0]) (ofSix (-16) (1) (1) (-154) (-2) (-10))
  rw [delayed_prefix41]
  intro u v; rfl

private theorem delayed_cyclic41 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 41) := by decide +kernel

private theorem delayed_edge41_0 :
    EdgeChecks WitnessLStarData.delayed 41 0 ((WitnessLStarData.delayed.core 41).edges 0) := by decide +kernel

private theorem delayed_edge41_1 :
    EdgeChecks WitnessLStarData.delayed 41 1 ((WitnessLStarData.delayed.core 41).edges 1) := by decide +kernel

private theorem delayed_edge41_2 :
    EdgeChecks WitnessLStarData.delayed 41 2 ((WitnessLStarData.delayed.core 41).edges 2) := by decide +kernel

private theorem delayed_edge41_3 :
    EdgeChecks WitnessLStarData.delayed 41 3 ((WitnessLStarData.delayed.core 41).edges 3) := by decide +kernel

private theorem delayed_triangles41 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 41) = true := by decide +kernel

private theorem delayed_descent41 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 41) = true := by
  change allTriangleDescentsCheck (ofSix (-16) (1) (1) (-154) (-2) (-10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable42 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 42).word) (WitnessLStarData.delayed.node 42) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,2]) (ofSix (16) (1) (-11) (138) (-1366) (10))
  rw [delayed_prefix42]
  intro u v; rfl

private theorem delayed_cyclic42 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 42) := by decide +kernel

private theorem delayed_edge42_0 :
    EdgeChecks WitnessLStarData.delayed 42 0 ((WitnessLStarData.delayed.core 42).edges 0) := by decide +kernel

private theorem delayed_edge42_1 :
    EdgeChecks WitnessLStarData.delayed 42 1 ((WitnessLStarData.delayed.core 42).edges 1) := by decide +kernel

private theorem delayed_edge42_2 :
    EdgeChecks WitnessLStarData.delayed 42 2 ((WitnessLStarData.delayed.core 42).edges 2) := by decide +kernel

private theorem delayed_edge42_3 :
    EdgeChecks WitnessLStarData.delayed 42 3 ((WitnessLStarData.delayed.core 42).edges 3) := by decide +kernel

private theorem delayed_triangles42 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 42) = true := by decide +kernel

private theorem delayed_descent42 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 42) = true := by
  change allTriangleDescentsCheck (ofSix (16) (1) (-11) (138) (-1366) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable43 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 43).word) (WitnessLStarData.delayed.node 43) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,3,0,2]) (ofSix (-638) (11) (-10) (-58) (-6) (1))
  rw [delayed_prefix43]
  intro u v; rfl

private theorem delayed_cyclic43 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 43) := by decide +kernel

private theorem delayed_edge43_0 :
    EdgeChecks WitnessLStarData.delayed 43 0 ((WitnessLStarData.delayed.core 43).edges 0) := by decide +kernel

private theorem delayed_edge43_1 :
    EdgeChecks WitnessLStarData.delayed 43 1 ((WitnessLStarData.delayed.core 43).edges 1) := by decide +kernel

private theorem delayed_edge43_2 :
    EdgeChecks WitnessLStarData.delayed 43 2 ((WitnessLStarData.delayed.core 43).edges 2) := by decide +kernel

private theorem delayed_edge43_3 :
    EdgeChecks WitnessLStarData.delayed 43 3 ((WitnessLStarData.delayed.core 43).edges 3) := by decide +kernel

private theorem delayed_triangles43 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 43) = true := by decide +kernel

private theorem delayed_descent43 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 43) = true := by
  change allTriangleDescentsCheck (ofSix (-638) (11) (-10) (-58) (-6) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable44 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 44).word) (WitnessLStarData.delayed.node 44) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0,3]) (ofSix (14) (1) (-1) (-66) (30) (-2))
  rw [delayed_prefix44]
  intro u v; rfl

private theorem delayed_cyclic44 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 44) := by decide +kernel

private theorem delayed_edge44_0 :
    EdgeChecks WitnessLStarData.delayed 44 0 ((WitnessLStarData.delayed.core 44).edges 0) := by decide +kernel

private theorem delayed_edge44_1 :
    EdgeChecks WitnessLStarData.delayed 44 1 ((WitnessLStarData.delayed.core 44).edges 1) := by decide +kernel

private theorem delayed_edge44_2 :
    EdgeChecks WitnessLStarData.delayed 44 2 ((WitnessLStarData.delayed.core 44).edges 2) := by decide +kernel

private theorem delayed_edge44_3 :
    EdgeChecks WitnessLStarData.delayed 44 3 ((WitnessLStarData.delayed.core 44).edges 3) := by decide +kernel

private theorem delayed_triangles44 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 44) = true := by decide +kernel

private theorem delayed_descent44 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 44) = true := by
  change allTriangleDescentsCheck (ofSix (14) (1) (-1) (-66) (30) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable45 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 45).word) (WitnessLStarData.delayed.node 45) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,2,3,0]) (ofSix (-16) (3) (-1) (-66) (14) (1))
  rw [delayed_prefix45]
  intro u v; rfl

private theorem delayed_cyclic45 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 45) := by decide +kernel

private theorem delayed_edge45_0 :
    EdgeChecks WitnessLStarData.delayed 45 0 ((WitnessLStarData.delayed.core 45).edges 0) := by decide +kernel

private theorem delayed_edge45_1 :
    EdgeChecks WitnessLStarData.delayed 45 1 ((WitnessLStarData.delayed.core 45).edges 1) := by decide +kernel

private theorem delayed_edge45_2 :
    EdgeChecks WitnessLStarData.delayed 45 2 ((WitnessLStarData.delayed.core 45).edges 2) := by decide +kernel

private theorem delayed_edge45_3 :
    EdgeChecks WitnessLStarData.delayed 45 3 ((WitnessLStarData.delayed.core 45).edges 3) := by decide +kernel

private theorem delayed_triangles45 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 45) = true := by decide +kernel

private theorem delayed_descent45 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 45) = true := by
  change allTriangleDescentsCheck (ofSix (-16) (3) (-1) (-66) (14) (1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable46 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 46).word) (WitnessLStarData.delayed.node 46) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,2,1,2,0]) (ofSix (2) (-1) (2) (0) (10) (-9))
  rw [delayed_prefix46]
  intro u v; rfl

private theorem delayed_cyclic46 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 46) := by decide +kernel

private theorem delayed_edge46_0 :
    EdgeChecks WitnessLStarData.delayed 46 0 ((WitnessLStarData.delayed.core 46).edges 0) := by decide +kernel

private theorem delayed_edge46_1 :
    EdgeChecks WitnessLStarData.delayed 46 1 ((WitnessLStarData.delayed.core 46).edges 1) := by decide +kernel

private theorem delayed_edge46_2 :
    EdgeChecks WitnessLStarData.delayed 46 2 ((WitnessLStarData.delayed.core 46).edges 2) := by decide +kernel

private theorem delayed_edge46_3 :
    EdgeChecks WitnessLStarData.delayed 46 3 ((WitnessLStarData.delayed.core 46).edges 3) := by decide +kernel

private theorem delayed_triangles46 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 46) = true := by decide +kernel

private theorem delayed_descent46 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 46) = true := by
  change allTriangleDescentsCheck (ofSix (2) (-1) (2) (0) (10) (-9)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable47 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 47).word) (WitnessLStarData.delayed.node 47) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,2,3,0,2]) (ofSix (8) (-1) (1) (-2) (18) (-3))
  rw [delayed_prefix47]
  intro u v; rfl

private theorem delayed_cyclic47 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 47) := by decide +kernel

private theorem delayed_edge47_0 :
    EdgeChecks WitnessLStarData.delayed 47 0 ((WitnessLStarData.delayed.core 47).edges 0) := by decide +kernel

private theorem delayed_edge47_1 :
    EdgeChecks WitnessLStarData.delayed 47 1 ((WitnessLStarData.delayed.core 47).edges 1) := by decide +kernel

private theorem delayed_edge47_2 :
    EdgeChecks WitnessLStarData.delayed 47 2 ((WitnessLStarData.delayed.core 47).edges 2) := by decide +kernel

private theorem delayed_edge47_3 :
    EdgeChecks WitnessLStarData.delayed 47 3 ((WitnessLStarData.delayed.core 47).edges 3) := by decide +kernel

private theorem delayed_triangles47 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 47) = true := by decide +kernel

private theorem delayed_descent47 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 47) = true := by
  change allTriangleDescentsCheck (ofSix (8) (-1) (1) (-2) (18) (-3)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable48 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 48).word) (WitnessLStarData.delayed.node 48) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2,0,2,3,2]) (ofSix (-52) (-2) (3) (-8) (-18) (-1))
  rw [delayed_prefix59]
  intro u v; rfl

private theorem delayed_cyclic48 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 48) := by decide +kernel

private theorem delayed_edge48_0 :
    EdgeChecks WitnessLStarData.delayed 48 0 ((WitnessLStarData.delayed.core 48).edges 0) := by decide +kernel

private theorem delayed_edge48_1 :
    EdgeChecks WitnessLStarData.delayed 48 1 ((WitnessLStarData.delayed.core 48).edges 1) := by decide +kernel

private theorem delayed_edge48_2 :
    EdgeChecks WitnessLStarData.delayed 48 2 ((WitnessLStarData.delayed.core 48).edges 2) := by decide +kernel

private theorem delayed_edge48_3 :
    EdgeChecks WitnessLStarData.delayed 48 3 ((WitnessLStarData.delayed.core 48).edges 3) := by decide +kernel

private theorem delayed_triangles48 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 48) = true := by decide +kernel

private theorem delayed_descent48 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 48) = true := by
  change allTriangleDescentsCheck (ofSix (-52) (-2) (3) (-8) (-18) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable49 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 49).word) (WitnessLStarData.delayed.node 49) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0]) (ofSix (64) (-1) (-1) (6) (638) (-10))
  rw [delayed_prefix49]
  intro u v; rfl

private theorem delayed_cyclic49 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 49) := by decide +kernel

private theorem delayed_edge49_0 :
    EdgeChecks WitnessLStarData.delayed 49 0 ((WitnessLStarData.delayed.core 49).edges 0) := by decide +kernel

private theorem delayed_edge49_1 :
    EdgeChecks WitnessLStarData.delayed 49 1 ((WitnessLStarData.delayed.core 49).edges 1) := by decide +kernel

private theorem delayed_edge49_2 :
    EdgeChecks WitnessLStarData.delayed 49 2 ((WitnessLStarData.delayed.core 49).edges 2) := by decide +kernel

private theorem delayed_edge49_3 :
    EdgeChecks WitnessLStarData.delayed 49 3 ((WitnessLStarData.delayed.core 49).edges 3) := by decide +kernel

private theorem delayed_triangles49 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 49) = true := by decide +kernel

private theorem delayed_descent49 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 49) = true := by
  change allTriangleDescentsCheck (ofSix (64) (-1) (-1) (6) (638) (-10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable50 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 50).word) (WitnessLStarData.delayed.node 50) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,3]) (ofSix (-64) (11) (-1) (5682) (-574) (10))
  rw [delayed_prefix50]
  intro u v; rfl

private theorem delayed_cyclic50 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 50) := by decide +kernel

private theorem delayed_edge50_0 :
    EdgeChecks WitnessLStarData.delayed 50 0 ((WitnessLStarData.delayed.core 50).edges 0) := by decide +kernel

private theorem delayed_edge50_1 :
    EdgeChecks WitnessLStarData.delayed 50 1 ((WitnessLStarData.delayed.core 50).edges 1) := by decide +kernel

private theorem delayed_edge50_2 :
    EdgeChecks WitnessLStarData.delayed 50 2 ((WitnessLStarData.delayed.core 50).edges 2) := by decide +kernel

private theorem delayed_edge50_3 :
    EdgeChecks WitnessLStarData.delayed 50 3 ((WitnessLStarData.delayed.core 50).edges 3) := by decide +kernel

private theorem delayed_triangles50 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 50) = true := by decide +kernel

private theorem delayed_descent50 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 50) = true := by
  change allTriangleDescentsCheck (ofSix (-64) (11) (-1) (5682) (-574) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable51 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 51).word) (WitnessLStarData.delayed.node 51) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0,2]) (ofSix (138) (-1) (1) (154) (-1542) (10))
  rw [delayed_prefix51]
  intro u v; rfl

private theorem delayed_cyclic51 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 51) := by decide +kernel

private theorem delayed_edge51_0 :
    EdgeChecks WitnessLStarData.delayed 51 0 ((WitnessLStarData.delayed.core 51).edges 0) := by decide +kernel

private theorem delayed_edge51_1 :
    EdgeChecks WitnessLStarData.delayed 51 1 ((WitnessLStarData.delayed.core 51).edges 1) := by decide +kernel

private theorem delayed_edge51_2 :
    EdgeChecks WitnessLStarData.delayed 51 2 ((WitnessLStarData.delayed.core 51).edges 2) := by decide +kernel

private theorem delayed_edge51_3 :
    EdgeChecks WitnessLStarData.delayed 51 3 ((WitnessLStarData.delayed.core 51).edges 3) := by decide +kernel

private theorem delayed_triangles51 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 51) = true := by decide +kernel

private theorem delayed_descent51 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 51) = true := by
  change allTriangleDescentsCheck (ofSix (138) (-1) (1) (154) (-1542) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable52 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 52).word) (WitnessLStarData.delayed.node 52) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,2,0]) (ofSix (-16) (-1) (11) (138) (-1542) (-1))
  rw [delayed_prefix52]
  intro u v; rfl

private theorem delayed_cyclic52 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 52) := by decide +kernel

private theorem delayed_edge52_0 :
    EdgeChecks WitnessLStarData.delayed 52 0 ((WitnessLStarData.delayed.core 52).edges 0) := by decide +kernel

private theorem delayed_edge52_1 :
    EdgeChecks WitnessLStarData.delayed 52 1 ((WitnessLStarData.delayed.core 52).edges 1) := by decide +kernel

private theorem delayed_edge52_2 :
    EdgeChecks WitnessLStarData.delayed 52 2 ((WitnessLStarData.delayed.core 52).edges 2) := by decide +kernel

private theorem delayed_edge52_3 :
    EdgeChecks WitnessLStarData.delayed 52 3 ((WitnessLStarData.delayed.core 52).edges 3) := by decide +kernel

private theorem delayed_triangles52 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 52) = true := by decide +kernel

private theorem delayed_descent52 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 52) = true := by
  change allTriangleDescentsCheck (ofSix (-16) (-1) (11) (138) (-1542) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable53 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 53).word) (WitnessLStarData.delayed.node 53) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0,3,2,0,2]) (ofSix (-66) (-1) (3) (14) (-182) (-2))
  rw [delayed_prefix62]
  intro u v; rfl

private theorem delayed_cyclic53 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 53) := by decide +kernel

private theorem delayed_edge53_0 :
    EdgeChecks WitnessLStarData.delayed 53 0 ((WitnessLStarData.delayed.core 53).edges 0) := by decide +kernel

private theorem delayed_edge53_1 :
    EdgeChecks WitnessLStarData.delayed 53 1 ((WitnessLStarData.delayed.core 53).edges 1) := by decide +kernel

private theorem delayed_edge53_2 :
    EdgeChecks WitnessLStarData.delayed 53 2 ((WitnessLStarData.delayed.core 53).edges 2) := by decide +kernel

private theorem delayed_edge53_3 :
    EdgeChecks WitnessLStarData.delayed 53 3 ((WitnessLStarData.delayed.core 53).edges 3) := by decide +kernel

private theorem delayed_triangles53 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 53) = true := by decide +kernel

private theorem delayed_descent53 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 53) = true := by
  change allTriangleDescentsCheck (ofSix (-66) (-1) (3) (14) (-182) (-2)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable54 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 54).word) (WitnessLStarData.delayed.node 54) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0,3]) (ofSix (-574) (-1) (1) (6386) (-638) (10))
  rw [delayed_prefix55]
  intro u v; rfl

private theorem delayed_cyclic54 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 54) := by decide +kernel

private theorem delayed_edge54_0 :
    EdgeChecks WitnessLStarData.delayed 54 0 ((WitnessLStarData.delayed.core 54).edges 0) := by decide +kernel

private theorem delayed_edge54_1 :
    EdgeChecks WitnessLStarData.delayed 54 1 ((WitnessLStarData.delayed.core 54).edges 1) := by decide +kernel

private theorem delayed_edge54_2 :
    EdgeChecks WitnessLStarData.delayed 54 2 ((WitnessLStarData.delayed.core 54).edges 2) := by decide +kernel

private theorem delayed_edge54_3 :
    EdgeChecks WitnessLStarData.delayed 54 3 ((WitnessLStarData.delayed.core 54).edges 3) := by decide +kernel

private theorem delayed_triangles54 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 54) = true := by decide +kernel

private theorem delayed_descent54 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 54) = true := by
  change allTriangleDescentsCheck (ofSix (-574) (-1) (1) (6386) (-638) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable55 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 55).word) (WitnessLStarData.delayed.node 55) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,3,0]) (ofSix (64) (-11) (1) (6386) (-574) (-1))
  rw [delayed_prefix56]
  intro u v; rfl

private theorem delayed_cyclic55 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 55) := by decide +kernel

private theorem delayed_edge55_0 :
    EdgeChecks WitnessLStarData.delayed 55 0 ((WitnessLStarData.delayed.core 55).edges 0) := by decide +kernel

private theorem delayed_edge55_1 :
    EdgeChecks WitnessLStarData.delayed 55 1 ((WitnessLStarData.delayed.core 55).edges 1) := by decide +kernel

private theorem delayed_edge55_2 :
    EdgeChecks WitnessLStarData.delayed 55 2 ((WitnessLStarData.delayed.core 55).edges 2) := by decide +kernel

private theorem delayed_edge55_3 :
    EdgeChecks WitnessLStarData.delayed 55 3 ((WitnessLStarData.delayed.core 55).edges 3) := by decide +kernel

private theorem delayed_triangles55 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 55) = true := by decide +kernel

private theorem delayed_descent55 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 55) = true := by
  change allTriangleDescentsCheck (ofSix (64) (-11) (1) (6386) (-574) (-1)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable56 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 56).word) (WitnessLStarData.delayed.node 56) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0,2,3,0,3]) (ofSix (-1542) (11) (-1) (-16946) (138) (10))
  rw [delayed_prefix64]
  intro u v; rfl

private theorem delayed_cyclic56 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 56) := by decide +kernel

private theorem delayed_edge56_0 :
    EdgeChecks WitnessLStarData.delayed 56 0 ((WitnessLStarData.delayed.core 56).edges 0) := by decide +kernel

private theorem delayed_edge56_1 :
    EdgeChecks WitnessLStarData.delayed 56 1 ((WitnessLStarData.delayed.core 56).edges 1) := by decide +kernel

private theorem delayed_edge56_2 :
    EdgeChecks WitnessLStarData.delayed 56 2 ((WitnessLStarData.delayed.core 56).edges 2) := by decide +kernel

private theorem delayed_edge56_3 :
    EdgeChecks WitnessLStarData.delayed 56 3 ((WitnessLStarData.delayed.core 56).edges 3) := by decide +kernel

private theorem delayed_triangles56 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 56) = true := by decide +kernel

private theorem delayed_descent56 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 56) = true := by
  change allTriangleDescentsCheck (ofSix (-1542) (11) (-1) (-16946) (138) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_reachable57 :
    EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core 57).word) (WitnessLStarData.delayed.node 57) := by
  change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0,3,2,0,2]) (ofSix (6386) (1) (-11) (-574) (70182) (10))
  rw [delayed_prefix65]
  intro u v; rfl

private theorem delayed_cyclic57 : ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node 57) := by decide +kernel

private theorem delayed_edge57_0 :
    EdgeChecks WitnessLStarData.delayed 57 0 ((WitnessLStarData.delayed.core 57).edges 0) := by decide +kernel

private theorem delayed_edge57_1 :
    EdgeChecks WitnessLStarData.delayed 57 1 ((WitnessLStarData.delayed.core 57).edges 1) := by decide +kernel

private theorem delayed_edge57_2 :
    EdgeChecks WitnessLStarData.delayed 57 2 ((WitnessLStarData.delayed.core 57).edges 2) := by decide +kernel

private theorem delayed_edge57_3 :
    EdgeChecks WitnessLStarData.delayed 57 3 ((WitnessLStarData.delayed.core 57).edges 3) := by decide +kernel

private theorem delayed_triangles57 :
    TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node 57) = true := by decide +kernel

private theorem delayed_descent57 :
    allTriangleDescentsCheck (WitnessLStarData.delayed.node 57) = true := by
  change allTriangleDescentsCheck (ofSix (6386) (1) (-11) (-574) (70182) (10)) = true
  unfold allTriangleDescentsCheck
  apply decide_eq_true
  intro r
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;>
    simp [triangleDescentCheck, TriangleDecision.CyclicSigns, TriangleRegions.restrict,
      TriangleRegions.deleteVertex, ofSix, constructiveDescent, sortWeights]

private theorem delayed_strip0 : StripChecks WitnessLStarData.delayed (WitnessLStarData.delayed.strips (0 : Fin 4)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [0,1,3,2,0]) (WitnessLStarData.delayed.node 37)
    rw [delayed_prefix37]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

private theorem delayed_strip1 : StripChecks WitnessLStarData.delayed (WitnessLStarData.delayed.strips (1 : Fin 4)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,3,2,0,3]) (WitnessLStarData.delayed.node 44)
    rw [delayed_prefix44]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

private theorem delayed_strip2 : StripChecks WitnessLStarData.delayed (WitnessLStarData.delayed.strips (2 : Fin 4)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,1,2,3,0,2]) (WitnessLStarData.delayed.node 51)
    rw [delayed_prefix51]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

private theorem delayed_strip3 : StripChecks WitnessLStarData.delayed (WitnessLStarData.delayed.strips (3 : Fin 4)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) [2,0,1,3,2,0,3]) (WitnessLStarData.delayed.node 54)
    rw [delayed_prefix55]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

theorem delayed_reachable : ∀ i, EntriesEqual (applyWord (WitnessLStarData.delayed.node 0) (WitnessLStarData.delayed.core i).word) (WitnessLStarData.delayed.node i) := by
  intro i
  change Fin 58 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact delayed_reachable0
  · exact delayed_reachable1
  · exact delayed_reachable2
  · exact delayed_reachable3
  · exact delayed_reachable4
  · exact delayed_reachable5
  · exact delayed_reachable6
  · exact delayed_reachable7
  · exact delayed_reachable8
  · exact delayed_reachable9
  · exact delayed_reachable10
  · exact delayed_reachable11
  · exact delayed_reachable12
  · exact delayed_reachable13
  · exact delayed_reachable14
  · exact delayed_reachable15
  · exact delayed_reachable16
  · exact delayed_reachable17
  · exact delayed_reachable18
  · exact delayed_reachable19
  · exact delayed_reachable20
  · exact delayed_reachable21
  · exact delayed_reachable22
  · exact delayed_reachable23
  · exact delayed_reachable24
  · exact delayed_reachable25
  · exact delayed_reachable26
  · exact delayed_reachable27
  · exact delayed_reachable28
  · exact delayed_reachable29
  · exact delayed_reachable30
  · exact delayed_reachable31
  · exact delayed_reachable32
  · exact delayed_reachable33
  · exact delayed_reachable34
  · exact delayed_reachable35
  · exact delayed_reachable36
  · exact delayed_reachable37
  · exact delayed_reachable38
  · exact delayed_reachable39
  · exact delayed_reachable40
  · exact delayed_reachable41
  · exact delayed_reachable42
  · exact delayed_reachable43
  · exact delayed_reachable44
  · exact delayed_reachable45
  · exact delayed_reachable46
  · exact delayed_reachable47
  · exact delayed_reachable48
  · exact delayed_reachable49
  · exact delayed_reachable50
  · exact delayed_reachable51
  · exact delayed_reachable52
  · exact delayed_reachable53
  · exact delayed_reachable54
  · exact delayed_reachable55
  · exact delayed_reachable56
  · exact delayed_reachable57

theorem delayed_cyclic : ∀ i, ¬ForkPruning.FiniteAcyclic (WitnessLStarData.delayed.node i) := by
  intro i
  change Fin 58 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact delayed_cyclic0
  · exact delayed_cyclic1
  · exact delayed_cyclic2
  · exact delayed_cyclic3
  · exact delayed_cyclic4
  · exact delayed_cyclic5
  · exact delayed_cyclic6
  · exact delayed_cyclic7
  · exact delayed_cyclic8
  · exact delayed_cyclic9
  · exact delayed_cyclic10
  · exact delayed_cyclic11
  · exact delayed_cyclic12
  · exact delayed_cyclic13
  · exact delayed_cyclic14
  · exact delayed_cyclic15
  · exact delayed_cyclic16
  · exact delayed_cyclic17
  · exact delayed_cyclic18
  · exact delayed_cyclic19
  · exact delayed_cyclic20
  · exact delayed_cyclic21
  · exact delayed_cyclic22
  · exact delayed_cyclic23
  · exact delayed_cyclic24
  · exact delayed_cyclic25
  · exact delayed_cyclic26
  · exact delayed_cyclic27
  · exact delayed_cyclic28
  · exact delayed_cyclic29
  · exact delayed_cyclic30
  · exact delayed_cyclic31
  · exact delayed_cyclic32
  · exact delayed_cyclic33
  · exact delayed_cyclic34
  · exact delayed_cyclic35
  · exact delayed_cyclic36
  · exact delayed_cyclic37
  · exact delayed_cyclic38
  · exact delayed_cyclic39
  · exact delayed_cyclic40
  · exact delayed_cyclic41
  · exact delayed_cyclic42
  · exact delayed_cyclic43
  · exact delayed_cyclic44
  · exact delayed_cyclic45
  · exact delayed_cyclic46
  · exact delayed_cyclic47
  · exact delayed_cyclic48
  · exact delayed_cyclic49
  · exact delayed_cyclic50
  · exact delayed_cyclic51
  · exact delayed_cyclic52
  · exact delayed_cyclic53
  · exact delayed_cyclic54
  · exact delayed_cyclic55
  · exact delayed_cyclic56
  · exact delayed_cyclic57

theorem delayed_triangles : ∀ i, TriangleDecision.checkAllTrianglesMA (WitnessLStarData.delayed.node i) = true := by
  intro i
  change Fin 58 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact delayed_triangles0
  · exact delayed_triangles1
  · exact delayed_triangles2
  · exact delayed_triangles3
  · exact delayed_triangles4
  · exact delayed_triangles5
  · exact delayed_triangles6
  · exact delayed_triangles7
  · exact delayed_triangles8
  · exact delayed_triangles9
  · exact delayed_triangles10
  · exact delayed_triangles11
  · exact delayed_triangles12
  · exact delayed_triangles13
  · exact delayed_triangles14
  · exact delayed_triangles15
  · exact delayed_triangles16
  · exact delayed_triangles17
  · exact delayed_triangles18
  · exact delayed_triangles19
  · exact delayed_triangles20
  · exact delayed_triangles21
  · exact delayed_triangles22
  · exact delayed_triangles23
  · exact delayed_triangles24
  · exact delayed_triangles25
  · exact delayed_triangles26
  · exact delayed_triangles27
  · exact delayed_triangles28
  · exact delayed_triangles29
  · exact delayed_triangles30
  · exact delayed_triangles31
  · exact delayed_triangles32
  · exact delayed_triangles33
  · exact delayed_triangles34
  · exact delayed_triangles35
  · exact delayed_triangles36
  · exact delayed_triangles37
  · exact delayed_triangles38
  · exact delayed_triangles39
  · exact delayed_triangles40
  · exact delayed_triangles41
  · exact delayed_triangles42
  · exact delayed_triangles43
  · exact delayed_triangles44
  · exact delayed_triangles45
  · exact delayed_triangles46
  · exact delayed_triangles47
  · exact delayed_triangles48
  · exact delayed_triangles49
  · exact delayed_triangles50
  · exact delayed_triangles51
  · exact delayed_triangles52
  · exact delayed_triangles53
  · exact delayed_triangles54
  · exact delayed_triangles55
  · exact delayed_triangles56
  · exact delayed_triangles57

theorem delayed_descents : ∀ i, allTriangleDescentsCheck (WitnessLStarData.delayed.node i) = true := by
  intro i
  change Fin 58 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact delayed_descent0
  · exact delayed_descent1
  · exact delayed_descent2
  · exact delayed_descent3
  · exact delayed_descent4
  · exact delayed_descent5
  · exact delayed_descent6
  · exact delayed_descent7
  · exact delayed_descent8
  · exact delayed_descent9
  · exact delayed_descent10
  · exact delayed_descent11
  · exact delayed_descent12
  · exact delayed_descent13
  · exact delayed_descent14
  · exact delayed_descent15
  · exact delayed_descent16
  · exact delayed_descent17
  · exact delayed_descent18
  · exact delayed_descent19
  · exact delayed_descent20
  · exact delayed_descent21
  · exact delayed_descent22
  · exact delayed_descent23
  · exact delayed_descent24
  · exact delayed_descent25
  · exact delayed_descent26
  · exact delayed_descent27
  · exact delayed_descent28
  · exact delayed_descent29
  · exact delayed_descent30
  · exact delayed_descent31
  · exact delayed_descent32
  · exact delayed_descent33
  · exact delayed_descent34
  · exact delayed_descent35
  · exact delayed_descent36
  · exact delayed_descent37
  · exact delayed_descent38
  · exact delayed_descent39
  · exact delayed_descent40
  · exact delayed_descent41
  · exact delayed_descent42
  · exact delayed_descent43
  · exact delayed_descent44
  · exact delayed_descent45
  · exact delayed_descent46
  · exact delayed_descent47
  · exact delayed_descent48
  · exact delayed_descent49
  · exact delayed_descent50
  · exact delayed_descent51
  · exact delayed_descent52
  · exact delayed_descent53
  · exact delayed_descent54
  · exact delayed_descent55
  · exact delayed_descent56
  · exact delayed_descent57

theorem delayed_edges : ∀ i k, EdgeChecks WitnessLStarData.delayed i k ((WitnessLStarData.delayed.core i).edges k) := by
  intro i k
  change Fin 58 at i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge0_0
    · exact delayed_edge0_1
    · exact delayed_edge0_2
    · exact delayed_edge0_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge1_0
    · exact delayed_edge1_1
    · exact delayed_edge1_2
    · exact delayed_edge1_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge2_0
    · exact delayed_edge2_1
    · exact delayed_edge2_2
    · exact delayed_edge2_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge3_0
    · exact delayed_edge3_1
    · exact delayed_edge3_2
    · exact delayed_edge3_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge4_0
    · exact delayed_edge4_1
    · exact delayed_edge4_2
    · exact delayed_edge4_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge5_0
    · exact delayed_edge5_1
    · exact delayed_edge5_2
    · exact delayed_edge5_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge6_0
    · exact delayed_edge6_1
    · exact delayed_edge6_2
    · exact delayed_edge6_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge7_0
    · exact delayed_edge7_1
    · exact delayed_edge7_2
    · exact delayed_edge7_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge8_0
    · exact delayed_edge8_1
    · exact delayed_edge8_2
    · exact delayed_edge8_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge9_0
    · exact delayed_edge9_1
    · exact delayed_edge9_2
    · exact delayed_edge9_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge10_0
    · exact delayed_edge10_1
    · exact delayed_edge10_2
    · exact delayed_edge10_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge11_0
    · exact delayed_edge11_1
    · exact delayed_edge11_2
    · exact delayed_edge11_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge12_0
    · exact delayed_edge12_1
    · exact delayed_edge12_2
    · exact delayed_edge12_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge13_0
    · exact delayed_edge13_1
    · exact delayed_edge13_2
    · exact delayed_edge13_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge14_0
    · exact delayed_edge14_1
    · exact delayed_edge14_2
    · exact delayed_edge14_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge15_0
    · exact delayed_edge15_1
    · exact delayed_edge15_2
    · exact delayed_edge15_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge16_0
    · exact delayed_edge16_1
    · exact delayed_edge16_2
    · exact delayed_edge16_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge17_0
    · exact delayed_edge17_1
    · exact delayed_edge17_2
    · exact delayed_edge17_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge18_0
    · exact delayed_edge18_1
    · exact delayed_edge18_2
    · exact delayed_edge18_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge19_0
    · exact delayed_edge19_1
    · exact delayed_edge19_2
    · exact delayed_edge19_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge20_0
    · exact delayed_edge20_1
    · exact delayed_edge20_2
    · exact delayed_edge20_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge21_0
    · exact delayed_edge21_1
    · exact delayed_edge21_2
    · exact delayed_edge21_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge22_0
    · exact delayed_edge22_1
    · exact delayed_edge22_2
    · exact delayed_edge22_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge23_0
    · exact delayed_edge23_1
    · exact delayed_edge23_2
    · exact delayed_edge23_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge24_0
    · exact delayed_edge24_1
    · exact delayed_edge24_2
    · exact delayed_edge24_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge25_0
    · exact delayed_edge25_1
    · exact delayed_edge25_2
    · exact delayed_edge25_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge26_0
    · exact delayed_edge26_1
    · exact delayed_edge26_2
    · exact delayed_edge26_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge27_0
    · exact delayed_edge27_1
    · exact delayed_edge27_2
    · exact delayed_edge27_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge28_0
    · exact delayed_edge28_1
    · exact delayed_edge28_2
    · exact delayed_edge28_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge29_0
    · exact delayed_edge29_1
    · exact delayed_edge29_2
    · exact delayed_edge29_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge30_0
    · exact delayed_edge30_1
    · exact delayed_edge30_2
    · exact delayed_edge30_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge31_0
    · exact delayed_edge31_1
    · exact delayed_edge31_2
    · exact delayed_edge31_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge32_0
    · exact delayed_edge32_1
    · exact delayed_edge32_2
    · exact delayed_edge32_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge33_0
    · exact delayed_edge33_1
    · exact delayed_edge33_2
    · exact delayed_edge33_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge34_0
    · exact delayed_edge34_1
    · exact delayed_edge34_2
    · exact delayed_edge34_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge35_0
    · exact delayed_edge35_1
    · exact delayed_edge35_2
    · exact delayed_edge35_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge36_0
    · exact delayed_edge36_1
    · exact delayed_edge36_2
    · exact delayed_edge36_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge37_0
    · exact delayed_edge37_1
    · exact delayed_edge37_2
    · exact delayed_edge37_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge38_0
    · exact delayed_edge38_1
    · exact delayed_edge38_2
    · exact delayed_edge38_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge39_0
    · exact delayed_edge39_1
    · exact delayed_edge39_2
    · exact delayed_edge39_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge40_0
    · exact delayed_edge40_1
    · exact delayed_edge40_2
    · exact delayed_edge40_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge41_0
    · exact delayed_edge41_1
    · exact delayed_edge41_2
    · exact delayed_edge41_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge42_0
    · exact delayed_edge42_1
    · exact delayed_edge42_2
    · exact delayed_edge42_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge43_0
    · exact delayed_edge43_1
    · exact delayed_edge43_2
    · exact delayed_edge43_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge44_0
    · exact delayed_edge44_1
    · exact delayed_edge44_2
    · exact delayed_edge44_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge45_0
    · exact delayed_edge45_1
    · exact delayed_edge45_2
    · exact delayed_edge45_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge46_0
    · exact delayed_edge46_1
    · exact delayed_edge46_2
    · exact delayed_edge46_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge47_0
    · exact delayed_edge47_1
    · exact delayed_edge47_2
    · exact delayed_edge47_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge48_0
    · exact delayed_edge48_1
    · exact delayed_edge48_2
    · exact delayed_edge48_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge49_0
    · exact delayed_edge49_1
    · exact delayed_edge49_2
    · exact delayed_edge49_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge50_0
    · exact delayed_edge50_1
    · exact delayed_edge50_2
    · exact delayed_edge50_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge51_0
    · exact delayed_edge51_1
    · exact delayed_edge51_2
    · exact delayed_edge51_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge52_0
    · exact delayed_edge52_1
    · exact delayed_edge52_2
    · exact delayed_edge52_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge53_0
    · exact delayed_edge53_1
    · exact delayed_edge53_2
    · exact delayed_edge53_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge54_0
    · exact delayed_edge54_1
    · exact delayed_edge54_2
    · exact delayed_edge54_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge55_0
    · exact delayed_edge55_1
    · exact delayed_edge55_2
    · exact delayed_edge55_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge56_0
    · exact delayed_edge56_1
    · exact delayed_edge56_2
    · exact delayed_edge56_3
  ·
    change Fin 4 at k
    have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_edge57_0
    · exact delayed_edge57_1
    · exact delayed_edge57_2
    · exact delayed_edge57_3

theorem delayed_checks : Checks WitnessLStarData.delayed where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := delayed_reachable
  cyclic := delayed_cyclic
  strips := by
    intro s
    change Fin 4 at s
    have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact delayed_strip0
    · exact delayed_strip1
    · exact delayed_strip2
    · exact delayed_strip3
  edges := delayed_edges
  triangles := (decide_eq_true delayed_triangles).symm
  descents := fun _ => delayed_descents

theorem checks : LStar.Checks WitnessLStarData.delayed := delayed_checks

theorem accepted : LStar.accept WitnessLStarData.delayed = true :=
  (LStar.accept_iff _).mpr checks

theorem nma : ¬MutationAcyclic WitnessLStarData.delayed.initial.matrix :=
  LStar.checked_NMA _ checks

theorem global_triangles (w : List (Fin 4)) :
    TriangleRegions.AllTrianglesMA (applyWord WitnessLStarData.delayed.initial.matrix w) :=
  LStar.checked_global_triangles _ checks rfl w

#print axioms nma
#print axioms global_triangles
end QuiverProofs.WitnessLStarDelayed
