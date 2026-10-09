import QuiverProofs.UnitZeroStrip
import QuiverProofs.UnitPendantStrip
import QuiverProofs.RecursiveRegionSemantics

/-! Exact shared region presentation for the unit-zero and unit-pendant rules.
Each constructor carries the printed cone, and each region has both actual
entrance parents. -/
namespace QuiverProofs.UnitRegionData
open RecursiveRegions

inductive Region where
  | n (x : Int) (p : UnitZeroStrip.Parameters)
      (hp : UnitZeroStrip.Domain x p.u p.v p.w)
  | d (p : UnitPendantStrip.Parameters) (hp : UnitPendantStrip.parameterDomain p)

abbrev Index : Region → Type
  | .n _ _ _ => Nat × Fin 10
  | .d _ _ => Fin 10

abbrev state : (r : Region) → Index r → Matrix 4
  | .n x p _, i => UnitZeroStrip.strip x p i.1 i.2
  | .d p _, i => UnitPendantStrip.node p i

abbrev parent : (r : Region) → Fin 2 → Matrix 4
  | .n x p _, j => UnitZeroStrip.parent x p j
  | .d p _, j => UnitPendantStrip.parent p j

abbrev data : RegionData Region where
  Index := Index
  parentCount := fun _ => 2
  state := state
  parent := parent
  skew := by
    intro r i
    cases r with
    | n x p hp => exact UnitZeroStrip.strip_skew x p i.1 i.2
    | d p hp => exact UnitPendantStrip.node_skew p i
  parent_skew := by
    intro r j
    cases r with
    | n x p hp => exact UnitZeroStrip.parent_skew x p j
    | d p hp => exact UnitPendantStrip.parent_skew p j
  cyclic := by
    intro r i
    cases r with
    | n x p hp => exact UnitZeroStrip.strip_cyclic x p hp i.1 i.2
    | d p hp => exact UnitPendantStrip.node_cyclic p hp i

end QuiverProofs.UnitRegionData
