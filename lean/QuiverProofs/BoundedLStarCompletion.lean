import QuiverProofs.BoundedLStarChecks
import QuiverProofs.WitnessLStarDelayed
import QuiverProofs.LStarCoreConsequences
namespace QuiverProofs.BoundedLStarCompletion
open LStar LStarCoreConsequences
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem q013_identification : (⟨0,false⟩ : Frame).apply (BoundedLStarData.q013.node 0) = ofSix (-2) (-2) (-2) (-2) (1) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q013 : ¬MutationAcyclic (ofSix (-2) (-2) (-2) (-2) (1) (-2)) := by
  rw [←q013_identification]
  exact framed_node_NMA BoundedLStarData.q013 BoundedLStarChecks.q013_checks 0 ⟨0,false⟩

theorem q040_identification : (⟨18,true⟩ : Frame).apply (WitnessLStarData.delayed.node 5) = ofSix (-2) (-2) (-1) (-2) (1) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q040 : ¬MutationAcyclic (ofSix (-2) (-2) (-1) (-2) (1) (-2)) := by
  rw [←q040_identification]
  exact framed_node_NMA WitnessLStarData.delayed WitnessLStarDelayed.checks 5 ⟨18,true⟩

theorem q046_identification : (⟨21,false⟩ : Frame).apply (WitnessLStarData.delayed.node 7) = ofSix (-2) (-2) (-1) (-2) (2) (-1) := by funext i j; revert i j; decide +kernel
theorem nma_q046 : ¬MutationAcyclic (ofSix (-2) (-2) (-1) (-2) (2) (-1)) := by
  rw [←q046_identification]
  exact framed_node_NMA WitnessLStarData.delayed WitnessLStarDelayed.checks 7 ⟨21,false⟩

theorem q066_identification : (⟨0,false⟩ : Frame).apply (BoundedLStarData.q066.node 0) = ofSix (-2) (-2) (-1) (-1) (1) (-1) := by funext i j; revert i j; decide +kernel
theorem nma_q066 : ¬MutationAcyclic (ofSix (-2) (-2) (-1) (-1) (1) (-1)) := by
  rw [←q066_identification]
  exact framed_node_NMA BoundedLStarData.q066 BoundedLStarChecks.q066_checks 0 ⟨0,false⟩

theorem q070_identification : (⟨0,false⟩ : Frame).apply (BoundedLStarData.q070.node 0) = ofSix (-2) (-2) (-1) (-1) (2) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q070 : ¬MutationAcyclic (ofSix (-2) (-2) (-1) (-1) (2) (-2)) := by
  rw [←q070_identification]
  exact framed_node_NMA BoundedLStarData.q070 BoundedLStarChecks.q070_checks 0 ⟨0,false⟩

theorem q155_identification : (⟨15,true⟩ : Frame).apply (WitnessLStarData.delayed.node 7) = ofSix (-2) (-2) (1) (-2) (-2) (1) := by funext i j; revert i j; decide +kernel
theorem nma_q155 : ¬MutationAcyclic (ofSix (-2) (-2) (1) (-2) (-2) (1)) := by
  rw [←q155_identification]
  exact framed_node_NMA WitnessLStarData.delayed WitnessLStarDelayed.checks 7 ⟨15,true⟩

theorem q156_identification : (⟨22,true⟩ : Frame).apply (BoundedLStarData.q013.node 0) = ofSix (-2) (-2) (1) (-2) (-2) (2) := by funext i j; revert i j; decide +kernel
theorem nma_q156 : ¬MutationAcyclic (ofSix (-2) (-2) (1) (-2) (-2) (2)) := by
  rw [←q156_identification]
  exact framed_node_NMA BoundedLStarData.q013 BoundedLStarChecks.q013_checks 0 ⟨22,true⟩

theorem q179_identification : (⟨0,false⟩ : Frame).apply (BoundedLStarData.q179.node 0) = ofSix (-2) (-2) (1) (-1) (-2) (1) := by funext i j; revert i j; decide +kernel
theorem nma_q179 : ¬MutationAcyclic (ofSix (-2) (-2) (1) (-1) (-2) (1)) := by
  rw [←q179_identification]
  exact framed_node_NMA BoundedLStarData.q179 BoundedLStarChecks.q179_checks 0 ⟨0,false⟩

theorem q180_identification : (⟨10,true⟩ : Frame).apply (BoundedLStarData.q070.node 0) = ofSix (-2) (-2) (1) (-1) (-2) (2) := by funext i j; revert i j; decide +kernel
theorem nma_q180 : ¬MutationAcyclic (ofSix (-2) (-2) (1) (-1) (-2) (2)) := by
  rw [←q180_identification]
  exact framed_node_NMA BoundedLStarData.q070 BoundedLStarChecks.q070_checks 0 ⟨10,true⟩

theorem q222_identification : (⟨7,false⟩ : Frame).apply (WitnessLStarData.delayed.node 5) = ofSix (-2) (-2) (2) (-2) (-1) (1) := by funext i j; revert i j; decide +kernel
theorem nma_q222 : ¬MutationAcyclic (ofSix (-2) (-2) (2) (-2) (-1) (1)) := by
  rw [←q222_identification]
  exact framed_node_NMA WitnessLStarData.delayed WitnessLStarDelayed.checks 5 ⟨7,false⟩

theorem q267_identification : (⟨12,false⟩ : Frame).apply (BoundedLStarData.q179.node 3) = ofSix (-2) (-1) (-1) (-2) (1) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q267 : ¬MutationAcyclic (ofSix (-2) (-1) (-1) (-2) (1) (-2)) := by
  rw [←q267_identification]
  exact framed_node_NMA BoundedLStarData.q179 BoundedLStarChecks.q179_checks 3 ⟨12,false⟩

theorem q289_identification : (⟨13,true⟩ : Frame).apply (BoundedLStarData.q179.node 0) = ofSix (-2) (-1) (-1) (-1) (2) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q289 : ¬MutationAcyclic (ofSix (-2) (-1) (-1) (-1) (2) (-2)) := by
  rw [←q289_identification]
  exact framed_node_NMA BoundedLStarData.q179 BoundedLStarChecks.q179_checks 0 ⟨13,true⟩

theorem q436_identification : (⟨21,true⟩ : Frame).apply (BoundedLStarData.q179.node 3) = ofSix (-2) (-1) (1) (-1) (-2) (2) := by funext i j; revert i j; decide +kernel
theorem nma_q436 : ¬MutationAcyclic (ofSix (-2) (-1) (1) (-1) (-2) (2)) := by
  rw [←q436_identification]
  exact framed_node_NMA BoundedLStarData.q179 BoundedLStarChecks.q179_checks 3 ⟨21,true⟩

theorem q455_identification : (⟨0,false⟩ : Frame).apply (BoundedLStarData.q455.node 0) = ofSix (-2) (-1) (1) (0) (-2) (1) := by funext i j; revert i j; decide +kernel
theorem nma_q455 : ¬MutationAcyclic (ofSix (-2) (-1) (1) (0) (-2) (1)) := by
  rw [←q455_identification]
  exact framed_node_NMA BoundedLStarData.q455 BoundedLStarChecks.q455_checks 0 ⟨0,false⟩

theorem q462_identification : (⟨0,true⟩ : Frame).apply (BoundedLStarData.q455.node 1) = ofSix (-2) (-1) (1) (0) (0) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q462 : ¬MutationAcyclic (ofSix (-2) (-1) (1) (0) (0) (-2)) := by
  rw [←q462_identification]
  exact framed_node_NMA BoundedLStarData.q455 BoundedLStarChecks.q455_checks 1 ⟨0,true⟩

theorem q487_identification : (⟨7,true⟩ : Frame).apply (BoundedLStarData.q066.node 0) = ofSix (-2) (-1) (1) (1) (2) (-1) := by funext i j; revert i j; decide +kernel
theorem nma_q487 : ¬MutationAcyclic (ofSix (-2) (-1) (1) (1) (2) (-1)) := by
  rw [←q487_identification]
  exact framed_node_NMA BoundedLStarData.q066 BoundedLStarChecks.q066_checks 0 ⟨7,true⟩

theorem q511_identification : (⟨0,false⟩ : Frame).apply (BoundedLStarData.q511.node 0) = ofSix (-2) (-1) (2) (-1) (0) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q511 : ¬MutationAcyclic (ofSix (-2) (-1) (2) (-1) (0) (-2)) := by
  rw [←q511_identification]
  exact framed_node_NMA BoundedLStarData.q511 BoundedLStarChecks.q511_checks 0 ⟨0,false⟩

theorem q550_identification : (⟨7,false⟩ : Frame).apply (BoundedLStarData.q455.node 1) = ofSix (-2) (0) (0) (-1) (1) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q550 : ¬MutationAcyclic (ofSix (-2) (0) (0) (-1) (1) (-2)) := by
  rw [←q550_identification]
  exact framed_node_NMA BoundedLStarData.q455 BoundedLStarChecks.q455_checks 1 ⟨7,false⟩

theorem q569_identification : (⟨7,true⟩ : Frame).apply (BoundedLStarData.q511.node 0) = ofSix (-2) (0) (1) (-2) (1) (-2) := by funext i j; revert i j; decide +kernel
theorem nma_q569 : ¬MutationAcyclic (ofSix (-2) (0) (1) (-2) (1) (-2)) := by
  rw [←q569_identification]
  exact framed_node_NMA BoundedLStarData.q511 BoundedLStarChecks.q511_checks 0 ⟨7,true⟩

theorem q613_identification : (⟨6,true⟩ : Frame).apply (BoundedLStarData.q455.node 0) = ofSix (-2) (0) (2) (1) (-1) (-1) := by funext i j; revert i j; decide +kernel
theorem nma_q613 : ¬MutationAcyclic (ofSix (-2) (0) (2) (1) (-1) (-1)) := by
  rw [←q613_identification]
  exact framed_node_NMA BoundedLStarData.q455 BoundedLStarChecks.q455_checks 0 ⟨6,true⟩

end QuiverProofs.BoundedLStarCompletion
