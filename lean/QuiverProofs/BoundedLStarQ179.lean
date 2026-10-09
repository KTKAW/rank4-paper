import QuiverProofs.BoundedLStarQ179Split.Reachable
import QuiverProofs.BoundedLStarQ179Split.Cyclic
import QuiverProofs.BoundedLStarQ179Split.Triangles
import QuiverProofs.BoundedLStarQ179Split.Descents
import QuiverProofs.BoundedLStarQ179Split.Edges
import QuiverProofs.BoundedLStarQ179Split.Strip00
import QuiverProofs.BoundedLStarQ179Split.Strip01
import QuiverProofs.BoundedLStarQ179Split.Strip02
import QuiverProofs.BoundedLStarQ179Split.Strip03
import QuiverProofs.BoundedLStarQ179Split.Strip04
import QuiverProofs.BoundedLStarQ179Split.Strip05
import QuiverProofs.BoundedLStarQ179Split.Strip06
import QuiverProofs.BoundedLStarQ179Split.Strip07
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_checks : Checks BoundedLStarData.q179 where
  connected := by
    intro i
    change Fin 4 at i
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    all_goals decide +kernel
  entry := by decide +kernel
  originWord := rfl
  reachable := q179_reachable
  cyclic := q179_cyclic
  strips := by
    intro s
    change Fin 8 at s
    have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 ∨ s=6 ∨ s=7 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact q179_strip0
    · exact q179_strip1
    · exact q179_strip2
    · exact q179_strip3
    · exact q179_strip4
    · exact q179_strip5
    · exact q179_strip6
    · exact q179_strip7
  edges := q179_edges
  triangles := (decide_eq_true q179_triangles).symm
  descents := fun _ => q179_descents

end QuiverProofs.BoundedLStarChecks
