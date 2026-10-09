import QuiverProofs.BoundedLStarQ179Split.Prefix08
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix72 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,0] = (ofSix (6) (-18) (1) (107) (-1) (-16)) := by
  rw [show ([3,0,2,1,3,0] : List (Fin 4)) = [3,0,2,1,3] ++ [0] from rfl,
    applyWord_append,q179_prefix57]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix73 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,2] = (ofSix (12) (-18) (35) (1) (-1) (-2)) := by
  rw [show ([3,0,2,1,3,2] : List (Fin 4)) = [3,0,2,1,3] ++ [2] from rfl,
    applyWord_append,q179_prefix57]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix74 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,0] = (ofSix (86) (-8) (1) (677) (13) (-9)) := by
  rw [show ([0,1,0,1,0,2,0] : List (Fin 4)) = [0,1,0,1,0,2] ++ [0] from rfl,
    applyWord_append,q179_prefix60]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix75 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,3] = (ofSix (-99) (8) (1) (2) (-13) (1)) := by
  rw [show ([0,1,0,1,0,2,3] : List (Fin 4)) = [0,1,0,1,0,2] ++ [3] from rfl,
    applyWord_append,q179_prefix60]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix76 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,2,3] = (ofSix (-53) (-1) (3) (-11) (-13) (-1)) := by
  rw [show ([0,1,0,2,0,2,3] : List (Fin 4)) = [0,1,0,2,0,2] ++ [3] from rfl,
    applyWord_append,q179_prefix61]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix77 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,3,2] = (ofSix (-53) (2) (1) (-24) (11) (-1)) := by
  rw [show ([0,1,0,2,0,3,2] : List (Fin 4)) = [0,1,0,2,0,3] ++ [2] from rfl,
    applyWord_append,q179_prefix62]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix78 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,1,0,2] = (ofSix (1) (-1) (12) (3) (-35) (6)) := by
  rw [show ([0,3,2,0,1,0,2] : List (Fin 4)) = [0,3,2,0,1,0] ++ [2] from rfl,
    applyWord_append,q179_prefix63]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix79 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,3,0,2] = (ofSix (6) (-1) (2) (18) (-35) (1)) := by
  rw [show ([0,3,2,0,3,0,2] : List (Fin 4)) = [0,3,2,0,3,0] ++ [2] from rfl,
    applyWord_append,q179_prefix64]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
