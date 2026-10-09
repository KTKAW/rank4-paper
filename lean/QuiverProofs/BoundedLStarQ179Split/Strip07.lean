import QuiverProofs.BoundedLStarQ179Split.Prefix11
namespace QuiverProofs.BoundedLStarChecks
open LStar CertificateSearch
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

theorem q179_strip7 : StripChecks BoundedLStarData.q179 (BoundedLStarData.q179.strips (7 : Fin 8)) := by
  refine ⟨by unfold GenericStrip.Domain; decide +kernel,by decide +kernel,?_,by decide +kernel,?_⟩
  · change EntriesEqual (applyWord (BoundedLStarData.q179.node 0) [0,1,0,1,0,2,3,0]) (BoundedLStarData.q179.node 85)
    rw [q179_prefix86]
    decide +kernel
  · intro p
    change Fin 3 at p
    have h : p=0 ∨ p=1 ∨ p=2 := by omega
    rcases h with rfl|rfl|rfl
    all_goals decide +kernel

end QuiverProofs.BoundedLStarChecks
