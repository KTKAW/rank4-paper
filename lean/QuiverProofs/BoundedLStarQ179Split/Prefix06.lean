import QuiverProofs.BoundedLStarQ179Split.Prefix05
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix48 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,3] = (ofSix (12) (-1) (-2) (-6) (7) (-1)) := by
  rw [show ([0,3,2,0,3] : List (Fin 4)) = [0,3,2,0] ++ [3] from rfl,
    applyWord_append,q179_prefix32]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix49 : applyWord (BoundedLStarData.q179.node 0) [1,3,1,2,3] = (ofSix (4) (-71) (26) (-2) (1) (-3)) := by
  rw [show ([1,3,1,2,3] : List (Fin 4)) = [1,3,1,2] ++ [3] from rfl,
    applyWord_append,q179_prefix33]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix50 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,0,3] = (ofSix (2) (1) (-1) (11) (0) (9)) := by
  rw [show ([2,0,1,0,3] : List (Fin 4)) = [2,0,1,0] ++ [3] from rfl,
    applyWord_append,q179_prefix35]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix51 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0] = (ofSix (-38) (8) (1) (-299) (-43) (1)) := by
  rw [show ([2,0,1,2,0] : List (Fin 4)) = [2,0,1,2] ++ [0] from rfl,
    applyWord_append,q179_prefix36]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix52 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,3] = (ofSix (38) (-9) (1) (0) (5) (-1)) := by
  rw [show ([2,0,1,2,3] : List (Fin 4)) = [2,0,1,2] ++ [3] from rfl,
    applyWord_append,q179_prefix36]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix53 : applyWord (BoundedLStarData.q179.node 0) [2,0,2,3,0] = (ofSix (8) (1) (-3) (-5) (24) (2)) := by
  rw [show ([2,0,2,3,0] : List (Fin 4)) = [2,0,2,3] ++ [0] from rfl,
    applyWord_append,q179_prefix37]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix54 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,1] = (ofSix (6) (-52) (-7) (9) (1) (3)) := by
  rw [show ([3,0,2,0,1] : List (Fin 4)) = [3,0,2,0] ++ [1] from rfl,
    applyWord_append,q179_prefix39]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix55 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,3] = (ofSix (-6) (-1) (1) (-12) (1) (-3)) := by
  rw [show ([3,0,2,0,3] : List (Fin 4)) = [3,0,2,0] ++ [3] from rfl,
    applyWord_append,q179_prefix39]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
