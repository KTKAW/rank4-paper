import Rank4Round5.Verification.BridgeObligations
import QuiverProofs.FiniteLogic
import Rank4CoordinatorR2.EndpointBudget
import QuiverProofs.MAHasTotalProper4Completion
import QuiverProofs.ProperEndpoint

/-!
An explicit MA mutation orbit has no uniform bound on the shortest word to
an acyclic endpoint.  This refutes a fixed-depth enumeration of acyclic
mutation targets, not arbitrary fixed polynomial-sign formulas.
-/

namespace Rank4Round5.Verification
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Formula Rank4Round3

def coneSeed : Matrix 4 := Cone.quiver 2 1 1 ⟨1,0,1⟩

theorem coneSeed_skew : SkewSymmetric coneSeed := by
  simpa [coneSeed, Cone.quiver] using ofSix_skew (-2) (-1) 1 (-1) 0 (-1)

theorem coneSeed_acyclicized : Acyclic (applyWord coneSeed [3]) := by
  refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 1), ?_⟩
  decide

theorem coneSeed_MA : MutationAcyclic coneSeed := ⟨[3],coneSeed_acyclicized⟩

def coneSeedInput : Rank4Input := ⟨coneSeed,coneSeed_skew⟩

def coneDescendant (n : Nat) : Matrix 4 :=
  applyWord coneSeed (Cone.repeatedWord n)

theorem coneDescendant_skew (n : Nat) : SkewSymmetric (coneDescendant n) :=
  word_preserves_skew coneSeed (Cone.repeatedWord n) coneSeed_skew

theorem coneDescendant_MA (n : Nat) : MutationAcyclic (coneDescendant n) := by
  refine ⟨(Cone.repeatedWord n).reverse ++ [3], ?_⟩
  rw [applyWord_append]
  change Acyclic (applyWord
    (applyWord (applyWord coneSeed (Cone.repeatedWord n))
      (Cone.repeatedWord n).reverse) [3])
  rw [ProperObstructionSoundness.applyWord_undo]
  exact coneSeed_acyclicized

def shortCandidates (r : Nat) : List (Matrix 4) :=
  (ForkPruning.matrixBox (endpointHeightBudget coneSeedInput)).flatMap
    (fun E => FiniteLogic.ball E r)

theorem coneDescendant_escapes (r : Nat) :
    ∃ n : Nat, coneDescendant n ∉ shortCandidates r := by
  have hc : Cone.InCone 1 1 0 1 := by
    unfold Cone.InCone
    decide
  have hg : 2 ≤ Cone.growth 2 1 1 := by decide
  obtain ⟨n,hn⟩ := Cone.mutation_orbit_escapes_finite_relabelings
    2 1 1 ⟨1,0,1⟩ (by decide) (by decide) (by decide) hc hg
    (shortCandidates r)
  refine ⟨n, ?_⟩
  intro hmem
  exact hn (coneDescendant n) hmem id (by rfl)

private theorem acyclicEndpoint_mem_box (n : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord (coneDescendant n) w)) :
    applyWord (coneDescendant n) w ∈
      ForkPruning.matrixBox (endpointHeightBudget coneSeedInput) := by
  have hcomp : Acyclic (applyWord coneSeed (Cone.repeatedWord n ++ w)) := by
    simpa only [applyWord_append,coneDescendant] using ha
  have hh := acyclic_endpoint_budget
    MAHasTotalProper4Completion.maHasTotalProper4
    ProperEndpoint.endpointTopological4 coneSeedInput
    (Cone.repeatedWord n ++ w) hcomp
  have hs : SkewSymmetric (applyWord (coneDescendant n) w) :=
    word_preserves_skew (coneDescendant n) w (coneDescendant_skew n)
  exact height_mem_box _ hs _ (by simpa only [applyWord_append,coneDescendant] using hh)

theorem no_short_acyclic_word (r : Nat) :
    ∃ n : Nat, ∀ w : List (Fin 4), w.length ≤ r →
      ¬ Acyclic (applyWord (coneDescendant n) w) := by
  obtain ⟨n,hn⟩ := coneDescendant_escapes r
  refine ⟨n,?_⟩
  intro w hw ha
  let E := applyWord (coneDescendant n) w
  have hE : E ∈ ForkPruning.matrixBox (endpointHeightBudget coneSeedInput) :=
    acyclicEndpoint_mem_box n w ha
  have hb : applyWord E w.reverse ∈ FiniteLogic.ball E r :=
    FiniteLogic.word_mem_ball E w.reverse r (by simpa using hw)
  have hu : applyWord E w.reverse = coneDescendant n := by
    exact ProperObstructionSoundness.applyWord_undo (coneDescendant n) w
  rw [hu] at hb
  have hmem : coneDescendant n ∈ shortCandidates r := by
    exact List.mem_flatMap.mpr ⟨E,hE,hb⟩
  exact hn hmem

theorem no_uniform_acyclic_depth :
    ∀ r : Nat, ¬ UniformAcyclicDepth r := by
  intro r h
  obtain ⟨n,hn⟩ := no_short_acyclic_word r
  let D := coneDescendant n
  let q : SixTuple := upperTuple D
  have hD : ofTuple q = D := ofTuple_upperTuple D (coneDescendant_skew n)
  have hma : MutationAcyclic (ofTuple q) := by
    rw [hD]
    exact coneDescendant_MA n
  obtain ⟨w,hw,ha⟩ := h q hma
  rw [hD] at ha
  exact hn w hw ha

theorem no_fixed_uniform_acyclic_depth :
    ¬ ∃ r : Nat, UniformAcyclicDepth r := by
  rintro ⟨r,hr⟩
  exact no_uniform_acyclic_depth r hr

#print axioms coneSeed_acyclicized
#print axioms coneDescendant_MA
#print axioms coneDescendant_escapes
#print axioms no_short_acyclic_word
#print axioms no_uniform_acyclic_depth
#print axioms no_fixed_uniform_acyclic_depth

end Rank4Round5.Verification
