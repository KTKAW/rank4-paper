import QuiverProofs.ProperEndpointData
namespace QuiverProofs.ProperEndpointData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
 theorem valid_chunk12 : ∀ (offset : Fin 27) (i : Fin 6),
    Valid (chunkCode 12 offset) i (certificate (chunkCode 12 offset) i) := by decide
end QuiverProofs.ProperEndpointData
