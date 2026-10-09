import QuiverProofs.BoundedLStarQ179Split.Prefix04
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix40 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1] = (ofSix (-6) (16) (1) (-3) (1) (-2)) := by
  rw [show ([3,0,2,1] : List (Fin 4)) = [3,0,2] ++ [1] from rfl,
    applyWord_append,q179_prefix26]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix41 : applyWord (BoundedLStarData.q179.node 0) [3,1,3,0] = (ofSix (0) (7) (-1) (-7) (2) (2)) := by
  rw [show ([3,1,3,0] : List (Fin 4)) = [3,1,3] ++ [0] from rfl,
    applyWord_append,q179_prefix27]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix42 : applyWord (BoundedLStarData.q179.node 0) [3,2,0,1] = (ofSix (0) (-2) (3) (-3) (1) (-8)) := by
  rw [show ([3,2,0,1] : List (Fin 4)) = [3,2,0] ++ [1] from rfl,
    applyWord_append,q179_prefix28]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix43 : applyWord (BoundedLStarData.q179.node 0) [3,2,0,3] = (ofSix (3) (13) (-3) (3) (1) (5)) := by
  rw [show ([3,2,0,3] : List (Fin 4)) = [3,2,0] ++ [3] from rfl,
    applyWord_append,q179_prefix28]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix44 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0] = (ofSix (2) (-8) (-1) (11) (2) (1)) := by
  rw [show ([0,1,0,1,0] : List (Fin 4)) = [0,1,0,1] ++ [0] from rfl,
    applyWord_append,q179_prefix30]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix45 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,2] = (ofSix (38) (-8) (9) (5) (0) (-1)) := by
  rw [show ([0,1,0,1,2] : List (Fin 4)) = [0,1,0,1] ++ [2] from rfl,
    applyWord_append,q179_prefix30]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix46 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0] = (ofSix (8) (-2) (-1) (11) (13) (-1)) := by
  rw [show ([0,1,0,2,0] : List (Fin 4)) = [0,1,0,2] ++ [0] from rfl,
    applyWord_append,q179_prefix31]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix47 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,1] = (ofSix (2) (-1) (-12) (-1) (7) (-6)) := by
  rw [show ([0,3,2,0,1] : List (Fin 4)) = [0,3,2,0] ++ [1] from rfl,
    applyWord_append,q179_prefix32]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
