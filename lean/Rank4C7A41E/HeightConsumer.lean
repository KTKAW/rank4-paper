import Rank4C7A41E.BoundDecision
import Rank4Coordinator.HeightBound

/-! Conditional assembly of the Coordinator's finite-height reduction with
the executable search. No supplier of `HeightCoverage H` is asserted here.
-/
namespace Rank4C7A41E
open QuiverProofs

theorem witnessBound_of_heightCoverage (H : Rank4Input → Nat)
    (coverage : Rank4Coordinator.HeightCoverage H) :
    WitnessBound (Rank4Coordinator.lengthBound H) :=
  fun Q ma => Rank4Coordinator.word_bound_of_height_coverage H coverage Q ma

def classifyWithHeight (H : Rank4Input → Nat) (Q : Rank4Input) : Bool :=
  classifyWithBound (Rank4Coordinator.lengthBound H) Q

theorem classifyWithHeight_ma_iff (H : Rank4Input → Nat)
    (coverage : Rank4Coordinator.HeightCoverage H) (Q : Rank4Input) :
    classifyWithHeight H Q = true ↔ MutationAcyclic Q.val :=
  classifyWithBound_ma_iff _ (witnessBound_of_heightCoverage H coverage) Q

theorem classifyWithHeight_nma_iff (H : Rank4Input → Nat)
    (coverage : Rank4Coordinator.HeightCoverage H) (Q : Rank4Input) :
    classifyWithHeight H Q = false ↔ ¬ MutationAcyclic Q.val :=
  classifyWithBound_nma_iff _ (witnessBound_of_heightCoverage H coverage) Q

def decidableWithHeight (H : Rank4Input → Nat)
    (coverage : Rank4Coordinator.HeightCoverage H) (Q : Rank4Input) :
    Decidable (MutationAcyclic Q.val) :=
  decidableWithBound _ (witnessBound_of_heightCoverage H coverage) Q

#print axioms classifyWithHeight
#print axioms decidableWithHeight
#print axioms witnessBound_of_heightCoverage
#print axioms classifyWithHeight_ma_iff
#print axioms classifyWithHeight_nma_iff
end Rank4C7A41E
