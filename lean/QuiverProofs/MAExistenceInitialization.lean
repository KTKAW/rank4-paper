import QuiverProofs.MAExistenceCoordinator
import QuiverProofs.MAExistenceLiterature
import QuiverProofs.MAExistenceAlternative

/-! An explicit order certificate and its unrestricted acyclic initialization.
The colors are witnesses, not assumed to come from an arbitrary mutation word.
This module proves initialization, wiggle invariance, and properness. Updating
the certificate after mutation remains a separate mathematical obligation. -/
namespace QuiverProofs.MAExistenceInitialization
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open MAExistenceLiterature MAExistenceCoordinator MAExistenceAlternative

/-- All per-vertex auxiliary orders belong to the specified wiggle class. -/
def AuxiliaryCertificate (B : Matrix 4) (green : Colors) (p : CyclicOrder) : Prop :=
  ∀ k, ∃ q : CyclicOrder, WiggleEquivalent B p q ∧
    Compatible B green k q ∧ GreenBeforeRed green q

theorem auxiliaryCertificate_wiggle {B : Matrix 4} (hB : SkewSymmetric B)
    {green : Colors} {p q : CyclicOrder} (hw : WiggleEquivalent B p q)
    (hp : AuxiliaryCertificate B green p) : AuxiliaryCertificate B green q := by
  intro k
  obtain ⟨r, hpr, hr, hc⟩ := hp k
  exact ⟨r, .trans (wiggle_symmetric B hB hw) hpr, hr, hc⟩

theorem auxiliaryCertificate_proper {B : Matrix 4} {green : Colors}
    {p : CyclicOrder} (hp : AuxiliaryCertificate B green p) : ProperClass B p :=
  auxiliary_orders_properClass B green p hp

theorem allGreen_auxiliaryArrow (B : Matrix 4) (k i j : Fin 4) :
    AuxiliaryArrow B (fun _ => true) k i j ↔ 0 < B i j := by
  simp [AuxiliaryArrow]

/-- Every topological order initializes the actual auxiliary order certificate.
There are no support, weight, connectedness, or determinant assumptions. -/
theorem topological_auxiliaryCertificate (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) (hp : Topological B p) :
    AuxiliaryCertificate B (fun _ => true) p := by
  intro k
  refine ⟨p, .same (fun _ _ _ => Iff.rfl), ?_, ?_⟩
  · intro i j hij
    exact topological_arrows_increase B hB p hp i j
      ((allGreen_auxiliaryArrow B k i j).mp hij)
  · intro i j hi hj
    simp at hj

theorem acyclic_auxiliaryCertificate (B : Matrix 4) (hB : SkewSymmetric B)
    (hA : Acyclic B) : ∃ p : CyclicOrder,
    Topological B p ∧ AuxiliaryCertificate B (fun _ => true) p := by
  obtain ⟨p, hp⟩ := AcyclicTargets.acyclic_has_topological_coordinates B hB hA
  exact ⟨p, hp, topological_auxiliaryCertificate B hB p hp⟩

/-- Initialization supplies an actual proper mutation at every vertex.
This theorem deliberately makes no claim about the output certificate. -/
theorem auxiliaryCertificate_has_mutation (B : Matrix 4) (hB : SkewSymmetric B)
    (green : Colors) (p : CyclicOrder) (hp : AuxiliaryCertificate B green p)
    (k : Fin 4) : ∃ q : CyclicOrder, ProperMutation B p k q :=
  properClass_has_mutation B hB p (auxiliaryCertificate_proper hp) k

end QuiverProofs.MAExistenceInitialization
