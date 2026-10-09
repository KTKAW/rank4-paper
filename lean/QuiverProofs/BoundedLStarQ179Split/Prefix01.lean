import QuiverProofs.BoundedLStarQ179Split.Prefix00
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix8 : applyWord (BoundedLStarData.q179.node 0) [1,2] = (ofSix (-2) (4) (-3) (-1) (3) (-1)) := by
  rw [show ([1,2] : List (Fin 4)) = [1] ++ [2] from rfl,
    applyWord_append,q179_prefix2]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix9 : applyWord (BoundedLStarData.q179.node 0) [1,3] = (ofSix (-4) (-7) (3) (1) (-2) (-1)) := by
  rw [show ([1,3] : List (Fin 4)) = [1] ++ [3] from rfl,
    applyWord_append,q179_prefix2]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix10 : applyWord (BoundedLStarData.q179.node 0) [2,0] = (ofSix (2) (-2) (-1) (5) (0) (-1)) := by
  rw [show ([2,0] : List (Fin 4)) = [2] ++ [0] from rfl,
    applyWord_append,q179_prefix3]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix11 : applyWord (BoundedLStarData.q179.node 0) [2,1] = (ofSix (2) (2) (-3) (-1) (2) (-3)) := by
  rw [show ([2,1] : List (Fin 4)) = [2] ++ [1] from rfl,
    applyWord_append,q179_prefix3]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix12 : applyWord (BoundedLStarData.q179.node 0) [2,3] = (ofSix (0) (3) (-1) (1) (2) (1)) := by
  rw [show ([2,3] : List (Fin 4)) = [2] ++ [3] from rfl,
    applyWord_append,q179_prefix3]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix13 : applyWord (BoundedLStarData.q179.node 0) [3,0] = (ofSix (0) (2) (1) (-3) (2) (-1)) := by
  rw [show ([3,0] : List (Fin 4)) = [3] ++ [0] from rfl,
    applyWord_append,q179_prefix4]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix14 : applyWord (BoundedLStarData.q179.node 0) [3,1] = (ofSix (0) (-2) (-1) (3) (-2) (5)) := by
  rw [show ([3,1] : List (Fin 4)) = [3] ++ [1] from rfl,
    applyWord_append,q179_prefix4]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix15 : applyWord (BoundedLStarData.q179.node 0) [3,2] = (ofSix (0) (2) (-3) (3) (-1) (1)) := by
  rw [show ([3,2] : List (Fin 4)) = [3] ++ [2] from rfl,
    applyWord_append,q179_prefix4]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
