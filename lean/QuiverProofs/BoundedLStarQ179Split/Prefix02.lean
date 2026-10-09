import QuiverProofs.BoundedLStarQ179Split.Prefix01
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix16 : applyWord (BoundedLStarData.q179.node 0) [0,1,0] = (ofSix (2) (-2) (1) (5) (0) (1)) := by
  rw [show ([0,1,0] : List (Fin 4)) = [0,1] ++ [0] from rfl,
    applyWord_append,q179_prefix5]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix17 : applyWord (BoundedLStarData.q179.node 0) [0,1,2] = (ofSix (-2) (-2) (5) (-1) (3) (-3)) := by
  rw [show ([0,1,2] : List (Fin 4)) = [0,1] ++ [2] from rfl,
    applyWord_append,q179_prefix5]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix18 : applyWord (BoundedLStarData.q179.node 0) [0,2,1] = (ofSix (-4) (2) (5) (-1) (0) (-3)) := by
  rw [show ([0,2,1] : List (Fin 4)) = [0,2] ++ [1] from rfl,
    applyWord_append,q179_prefix6]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix19 : applyWord (BoundedLStarData.q179.node 0) [0,3,2] = (ofSix (2) (1) (-2) (1) (-3) (3)) := by
  rw [show ([0,3,2] : List (Fin 4)) = [0,3] ++ [2] from rfl,
    applyWord_append,q179_prefix7]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix20 : applyWord (BoundedLStarData.q179.node 0) [1,2,3] = (ofSix (-11) (4) (3) (2) (-3) (1)) := by
  rw [show ([1,2,3] : List (Fin 4)) = [1,2] ++ [3] from rfl,
    applyWord_append,q179_prefix8]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix21 : applyWord (BoundedLStarData.q179.node 0) [1,3,1] = (ofSix (4) (-7) (-5) (-1) (2) (-3)) := by
  rw [show ([1,3,1] : List (Fin 4)) = [1,3] ++ [1] from rfl,
    applyWord_append,q179_prefix9]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix22 : applyWord (BoundedLStarData.q179.node 0) [1,3,2] = (ofSix (-11) (7) (-4) (-1) (-2) (1)) := by
  rw [show ([1,3,2] : List (Fin 4)) = [1,3] ++ [2] from rfl,
    applyWord_append,q179_prefix9]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix23 : applyWord (BoundedLStarData.q179.node 0) [2,0,1] = (ofSix (-2) (8) (-1) (-5) (0) (-1)) := by
  rw [show ([2,0,1] : List (Fin 4)) = [2,0] ++ [1] from rfl,
    applyWord_append,q179_prefix10]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
