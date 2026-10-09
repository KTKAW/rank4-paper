import QuiverProofs.BoundedLStarQ179Split.Prefix02
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix24 : applyWord (BoundedLStarData.q179.node 0) [2,0,2] = (ofSix (-8) (2) (-3) (-5) (0) (1)) := by
  rw [show ([2,0,2] : List (Fin 4)) = [2,0] ++ [2] from rfl,
    applyWord_append,q179_prefix10]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix25 : applyWord (BoundedLStarData.q179.node 0) [3,0,1] = (ofSix (0) (2) (1) (3) (-2) (5)) := by
  rw [show ([3,0,1] : List (Fin 4)) = [3,0] ++ [1] from rfl,
    applyWord_append,q179_prefix13]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix26 : applyWord (BoundedLStarData.q179.node 0) [3,0,2] = (ofSix (6) (-2) (1) (3) (-1) (1)) := by
  rw [show ([3,0,2] : List (Fin 4)) = [3,0] ++ [2] from rfl,
    applyWord_append,q179_prefix13]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix27 : applyWord (BoundedLStarData.q179.node 0) [3,1,3] = (ofSix (0) (-7) (1) (-7) (2) (-5)) := by
  rw [show ([3,1,3] : List (Fin 4)) = [3,1] ++ [3] from rfl,
    applyWord_append,q179_prefix14]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix28 : applyWord (BoundedLStarData.q179.node 0) [3,2,0] = (ofSix (0) (-2) (3) (3) (-1) (-5)) := by
  rw [show ([3,2,0] : List (Fin 4)) = [3,2] ++ [0] from rfl,
    applyWord_append,q179_prefix15]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix29 : applyWord (BoundedLStarData.q179.node 0) [3,2,1] = (ofSix (0) (2) (-3) (-3) (1) (-2)) := by
  rw [show ([3,2,1] : List (Fin 4)) = [3,2] ++ [1] from rfl,
    applyWord_append,q179_prefix15]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix30 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1] = (ofSix (-2) (8) (1) (-5) (0) (1)) := by
  rw [show ([0,1,0,1] : List (Fin 4)) = [0,1,0] ++ [1] from rfl,
    applyWord_append,q179_prefix16]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix31 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,2] = (ofSix (-8) (2) (1) (-5) (5) (-1)) := by
  rw [show ([0,1,0,2] : List (Fin 4)) = [0,1,0] ++ [2] from rfl,
    applyWord_append,q179_prefix16]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
