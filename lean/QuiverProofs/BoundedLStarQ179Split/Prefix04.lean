import QuiverProofs.BoundedLStarQ179Split.Prefix03
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix32 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0] = (ofSix (-2) (-1) (2) (1) (-7) (1)) := by
  rw [show ([0,3,2,0] : List (Fin 4)) = [0,3,2] ++ [0] from rfl,
    applyWord_append,q179_prefix19]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix33 : applyWord (BoundedLStarData.q179.node 0) [1,3,1,2] = (ofSix (4) (7) (-26) (1) (-1) (3)) := by
  rw [show ([1,3,1,2] : List (Fin 4)) = [1,3,1] ++ [2] from rfl,
    applyWord_append,q179_prefix21]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix34 : applyWord (BoundedLStarData.q179.node 0) [1,3,2,1] = (ofSix (11) (-4) (-26) (1) (2) (1)) := by
  rw [show ([1,3,2,1] : List (Fin 4)) = [1,3,2] ++ [1] from rfl,
    applyWord_append,q179_prefix22]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix35 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,0] = (ofSix (2) (-8) (1) (11) (0) (-9)) := by
  rw [show ([2,0,1,0] : List (Fin 4)) = [2,0,1] ++ [0] from rfl,
    applyWord_append,q179_prefix23]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix36 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2] = (ofSix (38) (-8) (-1) (5) (-5) (1)) := by
  rw [show ([2,0,1,2] : List (Fin 4)) = [2,0,1] ++ [2] from rfl,
    applyWord_append,q179_prefix23]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix37 : applyWord (BoundedLStarData.q179.node 0) [2,0,2,3] = (ofSix (-8) (-1) (3) (-5) (0) (-1)) := by
  rw [show ([2,0,2,3] : List (Fin 4)) = [2,0,2] ++ [3] from rfl,
    applyWord_append,q179_prefix24]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix38 : applyWord (BoundedLStarData.q179.node 0) [3,0,1,3] = (ofSix (2) (2) (-1) (-7) (2) (-5)) := by
  rw [show ([3,0,1,3] : List (Fin 4)) = [3,0,1] ++ [3] from rfl,
    applyWord_append,q179_prefix25]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix39 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,0] = (ofSix (-6) (2) (-1) (-9) (-1) (3)) := by
  rw [show ([3,0,2,0] : List (Fin 4)) = [3,0,2] ++ [0] from rfl,
    applyWord_append,q179_prefix26]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
