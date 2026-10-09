import QuiverProofs.E3Core
import QuiverProofs.GenericRegionAdapter
import QuiverProofs.UnitRegionData

namespace QuiverProofs.E3EntryData
open E3Core TriangleRegions

/-- The six generic entrance cones, with the checked E3 parameters. -/
def genericSeed (j : Fin 6) : GenericRegionAdapter.Seed :=
  ⟨stripM j,stripSeed j,strip_domain j⟩

def zeroParameters (j : Fin 6) : UnitZeroStrip.Parameters :=
  ⟨(zeroSeed j).u,(zeroSeed j).v,(zeroSeed j).w⟩

theorem zero_parameters_domain (j : Fin 6) :
    UnitZeroStrip.Domain (zeroSeed j).x (zeroParameters j).u
      (zeroParameters j).v (zeroParameters j).w := zero_domain j

def zeroRegion (j : Fin 6) : UnitRegionData.Region :=
  .n (zeroSeed j).x (zeroParameters j) (zero_parameters_domain j)

def pendantParameters (j : Fin 2) : UnitPendantStrip.Parameters :=
  ⟨(pendantSeed j).d,(pendantSeed j).x,(pendantSeed j).y⟩

theorem pendant_parameters_domain (j : Fin 2) :
    UnitPendantStrip.parameterDomain (pendantParameters j) := by
  have h := pendant_domain j
  have hd := Int.le_max_left (pendantSeed j).d (pendantSeed j).x
  have hx := Int.le_max_right (pendantSeed j).d (pendantSeed j).x
  change 2 ≤ (pendantSeed j).d ∧ 2 ≤ (pendantSeed j).x ∧
    (pendantSeed j).d < (pendantSeed j).y ∧ (pendantSeed j).x < (pendantSeed j).y
  omega

def pendantRegion (j : Fin 2) : UnitRegionData.Region :=
  .d (pendantParameters j) (pendant_parameters_domain j)

theorem generic_state (j s : Fin 6) :
    GenericRegionAdapter.data.state (genericSeed j) (0,s) = stripPhase j s := rfl

theorem zero_state (j : Fin 6) (s : Fin 2) :
    UnitRegionData.data.state (zeroRegion j) (0,Fin.castLE (by decide) s) = zeroPhase j s := by
  have hs : s=0 ∨ s=1 := by omega
  rcases hs with rfl|rfl
  · rfl
  · change UnitZeroStrip.node (zeroSeed j).x (zeroSeed j).u (zeroSeed j).v
      (zeroSeed j).w 1 = mutate (UnitZeroStrip.node (zeroSeed j).x (zeroSeed j).u
      (zeroSeed j).v (zeroSeed j).w 0) 0
    exact (UnitZeroStrip.special_0 _ _ _ _ (zero_domain j)).symm

theorem pendant_state (j s : Fin 2) :
    UnitRegionData.data.state (pendantRegion j) (Fin.castLE (by decide) s) = pendantPhase j s := by
  have hs : s=0 ∨ s=1 := by omega
  rcases hs with rfl|rfl
  · rfl
  · change UnitPendantStrip.D1 (pendantSeed j).d (pendantSeed j).x (pendantSeed j).y =
      mutate (UnitPendantStrip.D0 (pendantSeed j).d (pendantSeed j).x (pendantSeed j).y) 0
    exact (UnitPendantStrip.D0_zero _ _ _ (pendant_parameters_domain j)).symm

theorem generic_parent_Target (j : Fin 6) (p : Fin 3) :
    Target (GenericRegionAdapter.data.parent (genericSeed j) p) := by
  have hp : p=0 ∨ p=1 ∨ p=2 := by omega
  rcases hp with rfl|rfl|rfl
  · exact strip_root_one_return j
  · exact strip_root_two_return j
  · exact strip_Q_zero_return j

theorem zero_parent_eq (j : Fin 6) (p : Fin 2) :
    UnitRegionData.data.parent (zeroRegion j) p = mutate (zeroPhase j p) 1 := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · change mutate (UnitRegionData.data.state (zeroRegion j) (0,Fin.castLE (by decide) (0 : Fin 2))) 1 = _
    rw [zero_state]
  · change mutate (UnitRegionData.data.state (zeroRegion j) (0,Fin.castLE (by decide) (1 : Fin 2))) 1 = _
    rw [zero_state]

theorem pendant_parent_eq (j p : Fin 2) :
    UnitRegionData.data.parent (pendantRegion j) p = mutate (pendantPhase j p) 1 := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · change mutate (UnitRegionData.data.state (pendantRegion j) (Fin.castLE (by decide) (0 : Fin 2))) 1 = _
    rw [pendant_state]
  · change mutate (UnitRegionData.data.state (pendantRegion j) (Fin.castLE (by decide) (1 : Fin 2))) 1 = _
    rw [pendant_state]

theorem zero_parent_Target (j : Fin 6) (p : Fin 2) :
    Target (UnitRegionData.data.parent (zeroRegion j) p) := by
  rw [zero_parent_eq]
  exact zero_parent j p

theorem pendant_parent_Target (j p : Fin 2) :
    Target (UnitRegionData.data.parent (pendantRegion j) p) := by
  rw [pendant_parent_eq]
  exact pendant_parent j p

theorem target_skew {B : Matrix 4} (h : Target B) : SkewSymmetric B := by
  induction h with
  | base i => exact all_skew i
  | strip j i => exact GenericStrip.phase_skew _ _ _ _ i
  | zero j s =>
    rw [←zero_state]
    exact UnitRegionData.data.skew _ _
  | pendant j s =>
    rw [←pendant_state]
    exact UnitRegionData.data.skew _ _
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem target_cyclic {B : Matrix 4} (h : Target B) : ¬ Acyclic B := by
  induction h with
  | base i => exact all_cyclic i
  | strip j i => exact GenericStrip.phase_cyclic _ _ _ _ (strip_domain j) i
  | zero j s =>
    rw [←zero_state]
    exact UnitRegionData.data.cyclic _ _
  | pendant j s =>
    rw [←pendant_state]
    exact UnitRegionData.data.cyclic _ _
  | framed _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih => exact fun ha => ih ((acyclic_reverse_iff _ (target_skew h)).mp ha)

theorem target_triangles {B : Matrix 4} (h : Target B) : AllTrianglesMA B := by
  induction h with
  | base i => exact all_triangles i
  | strip j i =>
    exact StripTriangles.phase_triangles _ _ _ _ (strip_domain j) (strip_root_triangles j) i
  | zero j s => exact zero_triangles j s
  | pendant j s => exact pendant_triangles j s
  | framed _ p ih => exact triangles_relabel _ p ih
  | reversed h ih => exact triangles_reverse _ (target_skew h) ih

end QuiverProofs.E3EntryData
