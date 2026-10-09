import MA4RestartEuler20261003.ResolvedModelEuler
import MA4RestartArrow20261003.AdjacentExceptionalFrame
import QuiverProofs.AcyclicTargets
import QuiverProofs.MAExistenceInitialization
import QuiverProofs.MAExistenceSupportChronology

/-! Initial ordered objects in the actual fixed weighted-quiver category.
The Ext fields are derived from the constructed projective resolution in
the subsequent part of this module. -/
namespace QuiverProofs.MA4RestartInitialOrderedFrame
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MAExistenceLiterature MAExistenceTeamBRootPositivity ProperOrder
open MA4RestartWeightedQuiverModel MA4RestartFreePathProjectives
open MA4RestartInitialSimples MA4RestartMatrixEuler
open MA4RestartResolvedModelEuler MA4RestartModelExt
open MA4RestartArrow20261003.AdjacentExceptionalFrame
open MAExistenceCoefficients MAExistenceSupportChronology MAExistenceTeamDJointSeed
open MAExistenceTeamBRootWordExchange
set_option maxHeartbeats 0

local instance actualHasExt (B : Matrix 4) (K : Type) [Field K] :
    HasExt.{0} (Representation B K) := representation_hasExt B K

def TopologicalOrder (B : Matrix 4) (p : CyclicOrder) : Prop :=
  ∀ a b : Fin 4, a < b → 0 ≤ B (p.toFun a) (p.toFun b)

theorem acyclic_topological_order (B : Matrix 4) (hB : SkewSymmetric B)
    (hA : Acyclic B) : ∃ p : CyclicOrder, TopologicalOrder B p := by
  obtain ⟨p, h01, h02, h03, h12, h13, h23⟩ :=
    AcyclicTargets.acyclic_has_topological_coordinates B hB hA
  refine ⟨p, ?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

theorem reverse_entry_nonpositive (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) (hp : TopologicalOrder B p)
    (a b : Fin 4) (hab : a < b) : B (p.toFun b) (p.toFun a) ≤ 0 := by
  have ht := hp a b hab
  have hs := hB (p.toFun a) (p.toFun b)
  omega

def initialObjects (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) : Fin 4 → Representation B K :=
  fun a => simpleRepresentation B K (p.toFun a)

theorem initial_scalar_endomorphisms (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) (a : Fin 4) :
    ∀ f : initialObjects B K p a ⟶ initialObjects B K p a,
      ∃ c : K, f = c • 𝟙 (initialObjects B K p a) :=
  simple_scalar_endomorphisms B K (p.toFun a)

theorem initial_identity_nonzero (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) (a : Fin 4) :
    (𝟙 (initialObjects B K p a) : initialObjects B K p a ⟶ initialObjects B K p a) ≠ 0 :=
  simple_identity_nonzero B K (p.toFun a)

theorem initial_finite_vertices (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) (a b : Fin 4) :
    Module.Finite K ((vertexFunctor B K b).obj (initialObjects B K p a)) :=
  simple_finite_vertices B K (p.toFun a) b

theorem initial_reverse_hom (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) (a b : Fin 4) (hab : a < b) :
    ∀ f : initialObjects B K p b ⟶ initialObjects B K p a, f = 0 := by
  apply simple_pair_hom_orthogonality B K (p.toFun b) (p.toFun a)
  intro h
  have he : b = a := p.injective h
  omega

theorem initial_dimensions (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) (a : Fin 4) :
    dimensionVector B K (initialObjects B K p a) =
      fun b => if b = p.toFun a then 1 else 0 := by
  funext b
  change (Module.finrank K ((vertexFunctor B K b).obj
    (simpleRepresentation B K (p.toFun a))) : Int) = _
  rw [simple_vertex_finrank]
  split <;> rfl

theorem initial_exceptional_frame (B : Matrix 4) (K : Type) [Field K]
    (hB : SkewSymmetric B) (p : CyclicOrder) (hp : TopologicalOrder B p) :
    ExceptionalFrame (vertexFunctor B K) (initialObjects B K p) := by
  refine ⟨?_, initial_scalar_endomorphisms B K p, initial_identity_nonzero B K p,
    initial_finite_vertices B K p, initial_reverse_hom B K p, ?_⟩
  · intro a
    exact initial_simple_rigid B K hB (p.toFun a)
  · intro a b hab
    exact initial_simple_ext_zero_of_nonpositive B K hB (p.toFun b) (p.toFun a)
      (reverse_entry_nonpositive B hB p hp a b hab)

/-- The ordered frame is initialized from actual simples without any
categorical-model, hereditary, Ext, or resolution premise. -/
theorem acyclic_initial_exceptional_frame (B : Matrix 4) (K : Type) [Field K]
    (hB : SkewSymmetric B) (hA : Acyclic B) :
    ∃ p : CyclicOrder, TopologicalOrder B p ∧
      ExceptionalFrame (vertexFunctor B K) (initialObjects B K p) ∧
      (∀ a, Simple (initialObjects B K p a)) ∧
      (∀ a, dimensionVector B K (initialObjects B K p a) =
        fun b => if b = p.toFun a then 1 else 0) := by
  obtain ⟨p,hp⟩ := acyclic_topological_order B hB hA
  exact ⟨p,hp,initial_exceptional_frame B K hB p hp,
    fun a => simple_is_simple B K (p.toFun a),initial_dimensions B K p⟩

theorem initial_compatible (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) (hp : TopologicalOrder B p) (k : Fin 4) :
    Compatible B (fun _ => true) k p := by
  have h6 : ProperObstructionSoundness.Topological B p :=
    ⟨hp 0 1 (by decide), hp 0 2 (by decide), hp 0 3 (by decide),
      hp 1 2 (by decide), hp 1 3 (by decide), hp 2 3 (by decide)⟩
  intro i j h
  exact MAExistenceCoordinator.topological_arrows_increase B hB p h6 i j
    ((MAExistenceInitialization.allGreen_auxiliaryArrow B k i j).mp h)

def initialColumns (p : CyclicOrder) : Matrix 4 := columnRelabel Cosquare.one p

theorem initial_dimension_columns (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) (a : Fin 4) :
    dimensionVector B K (initialObjects B K p a) = column (initialColumns p) a := by
  rw [initial_dimensions]
  rfl

theorem initial_ordered_root_frame (B U : Matrix 4) (hB : SkewSymmetric B)
    (hA : Acyclic B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B)
    (p : CyclicOrder) (hp : TopologicalOrder B p) :
    OrderedRootFrame B U (initialColumns p) := by
  have hg : columnColor (identityCoefficients : Matrix 4) = (fun _ => true) := by
    funext j
    exact color_green (identity_green j)
  have hc : Compatible (principalSeed B []).1
      (columnColor (principalSeed B []).2) 0 p := by
    change Compatible B (columnColor identityCoefficients) 0 p
    rw [hg]
    exact initial_compatible B hB p hp 0
  exact seedInv_compatible_orderedRootFrame B U hB hs ha [] (seedInv_nil B hB hA) 0 p hc

theorem initial_pair_hom_zero (B : Matrix 4) (K : Type) [Field K]
    (p : CyclicOrder) (a b : Fin 4) (hab : a ≠ b) :
    ∀ f : initialObjects B K p a ⟶ initialObjects B K p b, f = 0 := by
  apply simple_pair_hom_orthogonality B K (p.toFun a) (p.toFun b)
  exact fun h => hab (p.injective h)

/-- Actual objects and the genuine numerical frame coincide at the literal
empty principal history. Both Euler parts are the existing lattice semantics. -/
theorem acyclic_initial_joint_frame (B U : Matrix 4) (K : Type) [Field K]
    (hB : SkewSymmetric B) (hA : Acyclic B)
    (hs : Cosquare.add U (Cosquare.transpose U) = initialCompanion B)
    (ha : Cosquare.add U (Cosquare.scale (-1) (Cosquare.transpose U)) = reverse B) :
    ∃ p : CyclicOrder, TopologicalOrder B p ∧
      ExceptionalFrame (vertexFunctor B K) (initialObjects B K p) ∧
      OrderedRootFrame B U (initialColumns p) ∧
      (∀ a, dimensionVector B K (initialObjects B K p a) = column (initialColumns p) a) ∧
      (∀ a b, a ≠ b → ∀ f : initialObjects B K p a ⟶ initialObjects B K p b, f = 0) ∧
      SeedInv B [] := by
  obtain ⟨p,hp⟩ := acyclic_topological_order B hB hA
  exact ⟨p,hp,initial_exceptional_frame B K hB p hp,
    initial_ordered_root_frame B U hB hA hs ha p hp,
    initial_dimension_columns B K p,initial_pair_hom_zero B K p,seedInv_nil B hB hA⟩

#print initial_exceptional_frame
#print axioms acyclic_initial_exceptional_frame
#print acyclic_initial_joint_frame
#print axioms acyclic_initial_joint_frame

end QuiverProofs.MA4RestartInitialOrderedFrame
