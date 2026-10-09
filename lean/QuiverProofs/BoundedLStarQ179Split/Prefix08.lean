import QuiverProofs.BoundedLStarQ179Split.Prefix07
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix64 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,3,0] = (ofSix (-12) (1) (2) (-18) (-17) (-1)) := by
  rw [show ([0,3,2,0,3,0] : List (Fin 4)) = [0,3,2,0,3] ++ [0] from rfl,
    applyWord_append,q179_prefix48]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix65 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,0,3,2] = (ofSix (2) (-1) (8) (-11) (99) (-9)) := by
  rw [show ([2,0,1,0,3,2] : List (Fin 4)) = [2,0,1,0,3] ++ [2] from rfl,
    applyWord_append,q179_prefix50]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix66 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,2] = (ofSix (2354) (-8) (9) (299) (-43) (-1)) := by
  rw [show ([2,0,1,2,0,2] : List (Fin 4)) = [2,0,1,2,0] ++ [2] from rfl,
    applyWord_append,q179_prefix51]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix67 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,3] = (ofSix (5) (8) (-1) (-342) (43) (-1)) := by
  rw [show ([2,0,1,2,0,3] : List (Fin 4)) = [2,0,1,2,0] ++ [3] from rfl,
    applyWord_append,q179_prefix51]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix68 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,3,0] = (ofSix (-38) (9) (-1) (-342) (5) (8)) := by
  rw [show ([2,0,1,2,3,0] : List (Fin 4)) = [2,0,1,2,3] ++ [0] from rfl,
    applyWord_append,q179_prefix52]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix69 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,1,3] = (ofSix (-1) (-73) (7) (9) (-1) (-3)) := by
  rw [show ([3,0,2,0,1,3] : List (Fin 4)) = [3,0,2,0,1] ++ [3] from rfl,
    applyWord_append,q179_prefix54]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix70 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,3,1] = (ofSix (6) (-73) (1) (12) (-1) (9)) := by
  rw [show ([3,0,2,0,3,1] : List (Fin 4)) = [3,0,2,0,3] ++ [1] from rfl,
    applyWord_append,q179_prefix55]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix71 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,0,3] = (ofSix (-1) (-16) (1) (107) (-7) (2)) := by
  rw [show ([3,0,2,1,0,3] : List (Fin 4)) = [3,0,2,1,0] ++ [3] from rfl,
    applyWord_append,q179_prefix56]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
