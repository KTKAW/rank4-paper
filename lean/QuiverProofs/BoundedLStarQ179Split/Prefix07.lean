import QuiverProofs.BoundedLStarQ179Split.Prefix06
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix56 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,0] = (ofSix (6) (-16) (-1) (93) (7) (-2)) := by
  rw [show ([3,0,2,1,0] : List (Fin 4)) = [3,0,2,1] ++ [0] from rfl,
    applyWord_append,q179_prefix40]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix57 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3] = (ofSix (-6) (18) (-1) (-1) (-1) (2)) := by
  rw [show ([3,0,2,1,3] : List (Fin 4)) = [3,0,2,1] ++ [3] from rfl,
    applyWord_append,q179_prefix40]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix58 : applyWord (BoundedLStarData.q179.node 0) [3,2,0,1,3] = (ofSix (0) (22) (-3) (5) (-1) (8)) := by
  rw [show ([3,2,0,1,3] : List (Fin 4)) = [3,2,0,1] ++ [3] from rfl,
    applyWord_append,q179_prefix42]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix59 : applyWord (BoundedLStarData.q179.node 0) [3,2,0,3,1] = (ofSix (-3) (22) (0) (-3) (-1) (5)) := by
  rw [show ([3,2,0,3,1] : List (Fin 4)) = [3,2,0,3] ++ [1] from rfl,
    applyWord_append,q179_prefix43]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix60 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2] = (ofSix (-86) (8) (-1) (-11) (13) (-1)) := by
  rw [show ([0,1,0,1,0,2] : List (Fin 4)) = [0,1,0,1,0] ++ [2] from rfl,
    applyWord_append,q179_prefix44]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix61 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,2] = (ofSix (-14) (2) (-3) (-11) (13) (1)) := by
  rw [show ([0,1,0,2,0,2] : List (Fin 4)) = [0,1,0,2,0] ++ [2] from rfl,
    applyWord_append,q179_prefix46]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix62 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,3] = (ofSix (-5) (-2) (1) (24) (-13) (1)) := by
  rw [show ([0,1,0,2,0,3] : List (Fin 4)) = [0,1,0,2,0] ++ [3] from rfl,
    applyWord_append,q179_prefix46]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix63 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,1,0] = (ofSix (-2) (1) (12) (-3) (-17) (-6)) := by
  rw [show ([0,3,2,0,1,0] : List (Fin 4)) = [0,3,2,0,1] ++ [0] from rfl,
    applyWord_append,q179_prefix47]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
