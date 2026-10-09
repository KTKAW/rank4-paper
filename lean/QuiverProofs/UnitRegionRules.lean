import QuiverProofs.UnitPendantRegionRules
import QuiverProofs.UnitZeroRegionRules

/-! Complete N/D local rules in their common exact two-parent presentation.
The mutation rules and retained-triangle descent are independent structures. -/
namespace QuiverProofs.UnitRegionRules
open RecursiveRegions UnitRegionData TriangleRegions

def nEncoding (x : Int) (p : UnitZeroStrip.Parameters)
    (hp : UnitZeroStrip.Domain x p.u p.v p.w) :
    UnitZeroRegionRules.Encoding data (.n x p hp) x p where
  index := fun n i => (n,i)
  parentIndex := id
  state_eq := fun _ _ => rfl
  parent_eq := fun _ => rfl

theorem n_edges (x : Int) (p : UnitZeroStrip.Parameters)
    (hp : UnitZeroStrip.Domain x p.u p.v p.w) (i : Nat × Fin 10) (k : Fin 4) :
    LocalEdge data (.n x p hp) (mutate (data.state (.n x p hp) i) k) k :=
  UnitZeroRegionRules.local_edges data (.n x p hp) x p hp (nEncoding x p hp) i.1 i.2 k

def rules : RegionRules data where
  edges := by
    intro r i k
    cases r with
    | n x p hp => exact n_edges x p hp i k
    | d p hp => exact UnitPendantRegionRules.all_edges p hp i k

def rank : (r : Region) → data.Index r → Nat
  | .n _ _ _, i => UnitZeroStrip.descentRank i.1 i.2
  | .d _ _, i => UnitPendantStrip.level i

def triangleRules : TriangleRules data where
  rank := rank
  descent := by
    intro r i
    cases r with
    | n x p hp =>
      right
      exact UnitZeroRegionRules.local_triangle_descent data (.n x p hp) x p hp
        (nEncoding x p hp) (rank (.n x p hp)) (fun _ _ => rfl) i.1 i.2
    | d p hp => exact UnitPendantRegionRules.triangle_descent p hp i

/-- Every word starting in a supplied N/D region stays nonacyclic when all
actual parents are already safe in the cyclic core grammar. -/
theorem region_NMA (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (hc : ∀ B, core B → ¬Acyclic B)
    (he : ∀ B, core B → ∀ k, Safe data core (mutate B k))
    (r : Region) (hp : ∀ j, Safe data core (data.parent r j)) (i : data.Index r) :
    ¬MutationAcyclic (data.state r i) :=
  safe_NMA data rules core hs hc he (.region r hp i)

theorem region_global_triangle_avoidance (core : Matrix 4 → Prop)
    (hs : ∀ B, core B → SkewSymmetric B) (ht : ∀ B, core B → AllTrianglesMA B)
    (he : ∀ B, core B → ∀ k, Safe data core (mutate B k))
    (r : Region) (hp : ∀ j, Safe data core (data.parent r j)) (i : data.Index r)
    (word : List (Fin 4)) : AllTrianglesMA (applyWord (data.state r i) word) :=
  safe_global_triangle_avoidance data rules triangleRules core hs ht he (.region r hp i) word

end QuiverProofs.UnitRegionRules
