import MA4RestartCoordinator20261003.WeightedQuiverModel
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! Forgetting arrows gives the actual discrete family of vertex spaces.
This functor is faithful and exact. A family of pointwise splittings is
natural over this discrete index; no splitting in the path category follows. -/
namespace QuiverProofs.MA4RestartVertexRestriction
open CategoryTheory CategoryTheory.Limits
open QuiverProofs.MA4RestartWeightedQuiverModel
set_option maxHeartbeats 0
variable (B : Matrix 4) (K : Type) [Field K]

def vertexRestriction : Representation B K ⥤ (Discrete (Vertex B) ⥤ ModuleCat.{0} K) :=
  (Functor.whiskeringLeft (Discrete (Vertex B)) (Paths (Vertex B)) (ModuleCat.{0} K)).obj
    (Discrete.functor (fun v : Vertex B => (v : Paths (Vertex B))))

instance restrictionFaithful : (vertexRestriction B K).Faithful where
  map_injective h := by
    apply NatTrans.ext
    funext j
    exact congrArg (fun η => η.app (Discrete.mk j)) h

instance restrictionPreservesZero : (vertexRestriction B K).PreservesZeroMorphisms where
  map_zero X Y := rfl

instance restrictionPreservesLimits : PreservesLimitsOfSize.{0, 0} (vertexRestriction B K) where
  preservesLimitsOfShape {J} _ :=
    ⟨fun {D} => ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits
      intro j
      change IsLimit (((evaluation (Paths (Vertex B)) (ModuleCat.{0} K)).obj j.as).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

instance restrictionPreservesColimits : PreservesColimitsOfSize.{0, 0} (vertexRestriction B K) where
  preservesColimitsOfShape {J} _ :=
    ⟨fun {D} => ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits
      intro j
      change IsColimit (((evaluation (Paths (Vertex B)) (ModuleCat.{0} K)).obj j.as).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

theorem restriction_exact_iff (S : ShortComplex (Representation B K)) :
    (S.map (vertexRestriction B K)).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful (vertexRestriction B K)

#print axioms restriction_exact_iff
end QuiverProofs.MA4RestartVertexRestriction
