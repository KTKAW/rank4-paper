import QuiverProofs.E3EntryData
import QuiverProofs.UnitRegionRules
import QuiverProofs.L0Exclusion

/-! Unconditional closure of the printed E3 mutation class.  The finite
67-state core is connected to the generic strips and recursive N/D grammar
by every explicitly checked entrance parent. -/
namespace QuiverProofs.E3Completion
open RecursiveRegions E3Core E3EntryData TriangleRegions

abbrev Region := GenericRegionAdapter.Seed ⊕ UnitRegionData.Region

def data : RegionData Region := GenericRegionAdapter.data.sum UnitRegionData.data

def rules : RegionRules data := GenericRegionAdapter.rules.sum UnitRegionRules.rules

def triangleRules : TriangleRules data :=
  GenericRegionAdapter.triangleRules.sum UnitRegionRules.triangleRules

theorem attached_step (r : Region) (hp : ∀ p, Target (data.parent r p))
    (i : data.Index r) (k : Fin 4) : Safe data Target (mutate (data.state r i) k) :=
  localEdge_safe data Target r (fun p => Safe.central (hp p)) i k (rules.edges r i k)

theorem core_edges {B : Matrix 4} (h : Target B) (k : Fin 4) :
    Safe data Target (mutate B k) := by
  induction h generalizing k with
  | base i =>
    rcases E3Core.all_edges i k with hc | hf | hr
    · exact Safe.central hc
    · exact Safe.fork k (Safe.central (Target.base i)) hf
    · exact attach_root data Target (Safe.central (Target.base i)) k hr
  | strip j i =>
    rw [← generic_state j i]
    exact attached_step (.inl (genericSeed j)) (generic_parent_Target j) (0,i) k
  | zero j s =>
    rw [← zero_state j s]
    exact attached_step (.inr (zeroRegion j)) (zero_parent_Target j)
      (0,Fin.castLE (by decide) s) k
  | pendant j s =>
    rw [← pendant_state j s]
    exact attached_step (.inr (pendantRegion j)) (pendant_parent_Target j)
      (Fin.castLE (by decide) s) k
  | framed _ p ih =>
    rw [mutate_relabel]
    exact Safe.framed (ih (p.toFun k)) p
  | reversed _ ih =>
    rw [mutate_reverse]
    exact Safe.reversed (ih k)

theorem core_all_words {B : Matrix 4} (h : Target B) (word : List (Fin 4)) :
    Safe data Target (applyWord B word) :=
  safe_all_words data rules Target (fun _ h k => core_edges h k) word (Safe.central h)

theorem target_NMA {B : Matrix 4} (h : Target B) : ¬ MutationAcyclic B :=
  safe_NMA data rules Target (fun _ h => target_skew h) (fun _ h => target_cyclic h)
    (fun _ h k => core_edges h k) (Safe.central h)

theorem target_global_triangle_avoidance {B : Matrix 4} (h : Target B)
    (word : List (Fin 4)) : AllTrianglesMA (applyWord B word) :=
  safe_global_triangle_avoidance data rules triangleRules Target
    (fun _ h => target_skew h) (fun _ h => target_triangles h)
    (fun _ h k => core_edges h k) (Safe.central h) word

theorem E3_NMA : ¬ MutationAcyclic (node 0) := target_NMA (Target.base 0)

theorem nma_q476 : ¬ MutationAcyclic (ofSix (-2) (-1) 1 1 (-2) 2) := E3_NMA

theorem printed_E3_NMA : ¬ MutationAcyclic (ClassSeparation.printed 2) := E3_NMA

theorem E3_global_triangle_avoidance (word : List (Fin 4)) :
    AllTrianglesMA (applyWord (node 0) word) :=
  target_global_triangle_avoidance (Target.base 0) word

/-- The three conclusions are independent: all-word NMA, all-word induced
triangle MA, and exclusion from the original finite-core certificate language. -/
theorem E3_structural_package :
    ¬ MutationAcyclic (ofSix (-2) (-1) 1 1 (-2) 2) ∧
    (∀ word : List (Fin 4), AllTrianglesMA
      (applyWord (ofSix (-2) (-1) 1 1 (-2) 2) word)) ∧
    ¬ ExtendedWeakPairs.FiniteCoreExteriorCover (ofSix (-2) (-1) 1 1 (-2) 2) :=
  ⟨E3_NMA,E3_global_triangle_avoidance,ExtendedWeakPairs.E3_no_finite_core_exterior_cover⟩

theorem E3_counterexample :
    ¬ MutationAcyclic (ofSix (-2) (-1) 1 1 (-2) 2) ∧
    (∀ word : List (Fin 4), AllTrianglesMA
      (applyWord (ofSix (-2) (-1) 1 1 (-2) 2) word)) ∧
    (∀ c : CertificateSearch.RegionCertificate,
      CertificateSearch.acceptCertificate (ofSix (-2) (-1) 1 1 (-2) 2) c ≠ true) :=
  ⟨E3_NMA,E3_global_triangle_avoidance,L0Exclusion.E3_no_L0_certificate⟩

end QuiverProofs.E3Completion
