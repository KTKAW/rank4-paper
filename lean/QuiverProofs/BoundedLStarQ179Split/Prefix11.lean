import QuiverProofs.BoundedLStarQ179Split.Prefix10
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix88 : applyWord (BoundedLStarData.q179.node 0) [0,3,2,0,3,0,2,0] = (ofSix (-6) (1) (-2) (12) (-35) (3)) := by
  rw [show ([0,3,2,0,3,0,2,0] : List (Fin 4)) = [0,3,2,0,3,0,2] ++ [0] from rfl,
    applyWord_append,q179_prefix79]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix89 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,2,3,0] = (ofSix (-2741) (-1) (9) (299) (-24626) (-8)) := by
  rw [show ([2,0,1,2,0,2,3,0] : List (Fin 4)) = [2,0,1,2,0,2,3] ++ [0] from rfl,
    applyWord_append,q179_prefix80]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix90 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,2,3,1] = (ofSix (-47) (99) (12) (-1) (-1) (2)) := by
  rw [show ([3,0,2,1,3,2,3,1] : List (Fin 4)) = [3,0,2,1,3,2,3] ++ [1] from rfl,
    applyWord_append,q179_prefix84]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix91 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,0,3,2] = (ofSix (86) (-1) (8) (-794) (7133) (-9)) := by
  rw [show ([0,1,0,1,0,2,0,3,2] : List (Fin 4)) = [0,1,0,1,0,2,0,3] ++ [2] from rfl,
    applyWord_append,q179_prefix85]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix92 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,2,3,1,3] = (ofSix (-35) (99) (-12) (-3) (1) (-2)) := by
  rw [show ([3,0,2,1,3,2,3,1,3] : List (Fin 4)) = [3,0,2,1,3,2,3,1] ++ [3] from rfl,
    applyWord_append,q179_prefix90]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
