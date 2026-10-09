import QuiverProofs.ProperEndpointBatches.Batch00
import QuiverProofs.ProperEndpointBatches.Batch01
import QuiverProofs.ProperEndpointBatches.Batch02
import QuiverProofs.ProperEndpointBatches.Batch03
import QuiverProofs.ProperEndpointBatches.Batch04
import QuiverProofs.ProperEndpointBatches.Batch05
import QuiverProofs.ProperEndpointBatches.Batch06
import QuiverProofs.ProperEndpointBatches.Batch07
import QuiverProofs.ProperEndpointBatches.Batch08
import QuiverProofs.ProperEndpointBatches.Batch09
import QuiverProofs.ProperEndpointBatches.Batch10
import QuiverProofs.ProperEndpointBatches.Batch11
import QuiverProofs.ProperEndpointBatches.Batch12
import QuiverProofs.ProperEndpointBatches.Batch13
import QuiverProofs.ProperEndpointBatches.Batch14
import QuiverProofs.ProperEndpointBatches.Batch15
import QuiverProofs.ProperEndpointBatches.Batch16
import QuiverProofs.ProperEndpointBatches.Batch17
import QuiverProofs.ProperEndpointBatches.Batch18
import QuiverProofs.ProperEndpointBatches.Batch19
import QuiverProofs.ProperEndpointBatches.Batch20
import QuiverProofs.ProperEndpointBatches.Batch21
import QuiverProofs.ProperEndpointBatches.Batch22
import QuiverProofs.ProperEndpointBatches.Batch23
import QuiverProofs.ProperEndpointBatches.Batch24
import QuiverProofs.ProperEndpointBatches.Batch25
import QuiverProofs.ProperEndpointBatches.Batch26
namespace QuiverProofs.ProperEndpointData
theorem valid_all_chunks : ∀ (b o : Fin 27) (i : Fin 6),
    Valid (chunkCode b o) i (certificate (chunkCode b o) i) := by
  intro b
  have hb : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 ∨ b=8 ∨ b=9 ∨ b=10 ∨ b=11 ∨ b=12 ∨ b=13 ∨ b=14 ∨ b=15 ∨ b=16 ∨ b=17 ∨ b=18 ∨ b=19 ∨ b=20 ∨ b=21 ∨ b=22 ∨ b=23 ∨ b=24 ∨ b=25 ∨ b=26 := by omega
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid_chunk00
  · exact valid_chunk01
  · exact valid_chunk02
  · exact valid_chunk03
  · exact valid_chunk04
  · exact valid_chunk05
  · exact valid_chunk06
  · exact valid_chunk07
  · exact valid_chunk08
  · exact valid_chunk09
  · exact valid_chunk10
  · exact valid_chunk11
  · exact valid_chunk12
  · exact valid_chunk13
  · exact valid_chunk14
  · exact valid_chunk15
  · exact valid_chunk16
  · exact valid_chunk17
  · exact valid_chunk18
  · exact valid_chunk19
  · exact valid_chunk20
  · exact valid_chunk21
  · exact valid_chunk22
  · exact valid_chunk23
  · exact valid_chunk24
  · exact valid_chunk25
  · exact valid_chunk26
theorem certificate_valid (code : Fin 729) (i : Fin 6) : Valid code i (certificate code i) := by
  have h := valid_all_chunks (block code) (offset code) i
  simpa only [chunkCode_correct] using h
end QuiverProofs.ProperEndpointData
