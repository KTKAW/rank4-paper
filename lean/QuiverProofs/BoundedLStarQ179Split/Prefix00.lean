import QuiverProofs.BoundedLStarData
import QuiverProofs.LStarCertificate
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix0 : applyWord (BoundedLStarData.q179.node 0) [] = (ofSix (-2) (-2) (1) (-1) (-2) (1)) := by
  rfl

theorem q179_prefix1 : applyWord (BoundedLStarData.q179.node 0) [0] = (ofSix (2) (2) (-1) (-1) (0) (3)) := by
  rw [show ([0] : List (Fin 4)) = [] ++ [0] from rfl,
    applyWord_append,q179_prefix0]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix2 : applyWord (BoundedLStarData.q179.node 0) [1] = (ofSix (2) (-4) (-3) (1) (2) (1)) := by
  rw [show ([1] : List (Fin 4)) = [] ++ [1] from rfl,
    applyWord_append,q179_prefix0]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix3 : applyWord (BoundedLStarData.q179.node 0) [2] = (ofSix (-2) (2) (1) (1) (-2) (-1)) := by
  rw [show ([2] : List (Fin 4)) = [] ++ [2] from rfl,
    applyWord_append,q179_prefix0]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix4 : applyWord (BoundedLStarData.q179.node 0) [3] = (ofSix (0) (-2) (-1) (-3) (2) (-1)) := by
  rw [show ([3] : List (Fin 4)) = [] ++ [3] from rfl,
    applyWord_append,q179_prefix0]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix5 : applyWord (BoundedLStarData.q179.node 0) [0,1] = (ofSix (-2) (2) (-1) (1) (0) (3)) := by
  rw [show ([0,1] : List (Fin 4)) = [0] ++ [1] from rfl,
    applyWord_append,q179_prefix1]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix6 : applyWord (BoundedLStarData.q179.node 0) [0,2] = (ofSix (4) (-2) (5) (1) (0) (-3)) := by
  rw [show ([0,2] : List (Fin 4)) = [0] ++ [2] from rfl,
    applyWord_append,q179_prefix1]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix7 : applyWord (BoundedLStarData.q179.node 0) [0,3] = (ofSix (2) (-1) (1) (-1) (0) (-3)) := by
  rw [show ([0,3] : List (Fin 4)) = [0] ++ [3] from rfl,
    applyWord_append,q179_prefix1]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
