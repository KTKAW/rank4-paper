import QuiverProofs.BoundedLStarQ179Split.Prefix09
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_prefix80 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,2,3] = (ofSix (2741) (1) (-9) (299) (43) (1)) := by
  rw [show ([2,0,1,2,0,2,3] : List (Fin 4)) = [2,0,1,2,0,2] ++ [3] from rfl,
    applyWord_append,q179_prefix66]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix81 : applyWord (BoundedLStarData.q179.node 0) [2,0,1,2,0,3,2] = (ofSix (2741) (-8) (-1) (342) (-299) (1)) := by
  rw [show ([2,0,1,2,0,3,2] : List (Fin 4)) = [2,0,1,2,0,3] ++ [2] from rfl,
    applyWord_append,q179_prefix67]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix82 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,0,1,3,0] = (ofSix (1) (73) (-7) (9) (6) (508)) := by
  rw [show ([3,0,2,0,1,3,0] : List (Fin 4)) = [3,0,2,0,1,3] ++ [0] from rfl,
    applyWord_append,q179_prefix69]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix83 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,0,3,1] = (ofSix (1) (-16) (-6) (-107) (7) (-747)) := by
  rw [show ([3,0,2,1,0,3,1] : List (Fin 4)) = [3,0,2,1,0,3] ++ [1] from rfl,
    applyWord_append,q179_prefix71]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix84 : applyWord (BoundedLStarData.q179.node 0) [3,0,2,1,3,2,3] = (ofSix (47) (52) (-35) (1) (1) (2)) := by
  rw [show ([3,0,2,1,3,2,3] : List (Fin 4)) = [3,0,2,1,3,2] ++ [3] from rfl,
    applyWord_append,q179_prefix73]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix85 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,0,3] = (ofSix (86) (1) (-1) (794) (-13) (9)) := by
  rw [show ([0,1,0,1,0,2,0,3] : List (Fin 4)) = [0,1,0,1,0,2,0] ++ [3] from rfl,
    applyWord_append,q179_prefix74]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix86 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,3,0] = (ofSix (99) (-8) (-1) (794) (86) (1)) := by
  rw [show ([0,1,0,1,0,2,3,0] : List (Fin 4)) = [0,1,0,1,0,2,3] ++ [0] from rfl,
    applyWord_append,q179_prefix75]
  apply entriesEqual_eq
  decide +kernel

theorem q179_prefix87 : applyWord (BoundedLStarData.q179.node 0) [0,1,0,2,0,2,3,0] = (ofSix (53) (1) (-3) (-11) (146) (2)) := by
  rw [show ([0,1,0,2,0,2,3,0] : List (Fin 4)) = [0,1,0,2,0,2,3] ++ [0] from rfl,
    applyWord_append,q179_prefix76]
  apply entriesEqual_eq
  decide +kernel

end QuiverProofs.BoundedLStarChecks
