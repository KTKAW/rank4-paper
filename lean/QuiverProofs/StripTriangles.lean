import QuiverProofs.StripSemantics
import QuiverProofs.TriangleRegions
import QuiverProofs.ExtendedWeakPairs

/-! The triangle argument is separate from strip NMA: each selected inward
mutation retains every cyclic triangle, and descends to an earlier phase or
level. The initial root's triangle hypothesis is always explicit. -/
namespace QuiverProofs.StripTriangles
open GenericStrip TriangleRegions

def inward (i : Fin 6) : Fin 4 := match i.val with
  | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 1 | _ => 0

def deletionRank (i : Fin 6) (v : Fin 4) : Nat := match i.val, v.val with
  | 0, 0 => 1 | 0, 3 => 2
  | 1, 1 => 1 | 1, 3 => 2
  | 2, 2 => 1 | 2, 3 => 2
  | 3, 1 => 1 | 3, 3 => 2
  | 4, 3 => 1 | 4, 2 => 2
  | 5, 3 => 1 | 5, 2 => 2
  | _, _ => 0

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem phase_deletion (m a b c : Int) (h : Domain m a b c) (i : Fin 6) :
    DeletionAcyclic (phase m a b c i) (inward i) := by
  have hp := parameter_bounds m a b c h
  have hg := growth m a b c h
  have hc := preserves_domain m a b c h
  unfold Domain at hc
  obtain ⟨hm,hmb,hbc,hca⟩ := h
  refine ⟨deletionRank i,?_⟩
  intro u v hu hv huv
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases fin4 u with rfl|rfl|rfl|rfl <;>
    rcases fin4 v with rfl|rfl|rfl|rfl <;>
    simp_all [phase,root,phaseP,phaseQ,phaseS,phaseT,phaseV,ofSix,inward,deletionRank] <;> omega

theorem phase_triangles (m a b c : Int) (h : Domain m a b c)
    (hr : AllTrianglesMA (root m a b c)) (i : Fin 6) :
    AllTrianglesMA (phase m a b c i) := by
  have hP : AllTrianglesMA (phaseP m a b c) := by
    apply deletion_triangle_transfer _ 0 (phase_deletion m a b c h 1)
    change AllTrianglesMA (mutate (phaseP m a b c) 0)
    rwa [P_zero m a b c h]
  have hQ : AllTrianglesMA (phaseQ m a b c) := by
    apply deletion_triangle_transfer _ 1 (phase_deletion m a b c h 2)
    change AllTrianglesMA (mutate (phaseQ m a b c) 1)
    rwa [Q_one m a b c h]
  have hS : AllTrianglesMA (phaseS m a b c) := by
    apply deletion_triangle_transfer _ 2 (phase_deletion m a b c h 3)
    change AllTrianglesMA (mutate (phaseS m a b c) 2)
    rwa [S_two m a b c h]
  have hT : AllTrianglesMA (phaseT m a b c) := by
    apply deletion_triangle_transfer _ 1 (phase_deletion m a b c h 4)
    change AllTrianglesMA (mutate (phaseT m a b c) 1)
    rwa [T_one m a b c h]
  have hV : AllTrianglesMA (phaseV m a b c) := by
    apply deletion_triangle_transfer _ 0 (phase_deletion m a b c h 5)
    change AllTrianglesMA (mutate (phaseV m a b c) 0)
    rwa [V_zero m a b c h]
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact hr
  · exact hP
  · exact hQ
  · exact hS
  · exact hT
  · exact hV

theorem orbit_triangles (m : Int) (s : Cone.State) (hd : Domain m s.A s.H s.Z)
    (hr : AllTrianglesMA (root m s.A s.H s.Z)) (n : Nat) (i : Fin 6) :
    AllTrianglesMA (phase m (orbit m s n).A (orbit m s n).H (orbit m s n).Z i) := by
  have roots : ∀ n, AllTrianglesMA (root m (orbit m s n).A (orbit m s n).H (orbit m s n).Z) := by
    intro n
    induction n with
    | zero => exact hr
    | succ n ih =>
      have h := orbit_domain m s hd n
      apply deletion_triangle_transfer _ 2 (phase_deletion _ _ _ _ (orbit_domain m s hd (n+1)) 0)
      change AllTrianglesMA (mutate (root m (nextA _ _ _ _) (nextB _ _ _) (nextC _ _ _ _)) 2)
      rw [next_root_two _ _ _ _ h]
      exact phase_triangles _ _ _ _ h ih 2
  exact phase_triangles _ _ _ _ (orbit_domain m s hd n) (roots n) i

theorem core_triangles (m : Int) (s : Cone.State) (base : Matrix 4 → Prop)
    (hd : Domain m s.A s.H s.Z) (hs : ∀ B, base B → SkewSymmetric B)
    (ht : ∀ B, base B → AllTrianglesMA B) (hr : AllTrianglesMA (root m s.A s.H s.Z))
    {B : Matrix 4} (hB : StripSemantics.Core m s base B) : AllTrianglesMA B := by
  induction hB with
  | base h => exact ht _ h
  | strip n i => exact orbit_triangles m s hd hr n i
  | framed _ p ih => exact triangles_relabel _ p ih
  | reversed h ih => exact triangles_reverse _ (StripSemantics.core_skew m s base hs h) ih

theorem core_all_triangles (m : Int) (s : Cone.State) (base : Matrix 4 → Prop)
    (hd : Domain m s.A s.H s.Z) (hs : ∀ B, base B → SkewSymmetric B)
    (ht : ∀ B, base B → AllTrianglesMA B) (hr : AllTrianglesMA (root m s.A s.H s.Z))
    (he : ∀ B, base B → ∀ k, StripSemantics.Exit (StripSemantics.Core m s base) B k)
    (hR1 : StripSemantics.Core m s base (mutate (root m s.A s.H s.Z) 1))
    (hR2 : StripSemantics.Core m s base (mutate (root m s.A s.H s.Z) 2))
    (hQ0 : StripSemantics.Core m s base (mutate (phaseQ m s.A s.H s.Z) 0))
    (B : Matrix 4) (hB : StripSemantics.Core m s base B) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord B word) := by
  apply region_all_triangles_MA (StripSemantics.Core m s base)
  · exact fun B h => StripSemantics.core_skew m s base hs h
  · exact fun B h => core_triangles m s base hd hs ht hr h
  · exact fun B h k => StripSemantics.core_edges m s base hd he hR1 hR2 hQ0 h k
  · exact hB

/-- A strictly growing two-unit-pair ray excludes every finite old-language
core, independently of the NMA and triangle-avoidance obligations. -/
theorem no_finite_core_exterior_cover (m a b c : Int) (hd : Domain m a b c) :
    ¬ ExtendedWeakPairs.FiniteCoreExteriorCover (root m a b c) := by
  obtain ⟨hm,hmb,hbc,hca⟩ := hd
  have hma := Int.mul_le_mul_of_nonneg_right hm (show 0 ≤ a by omega)
  have hcone : Cone.InCone m a b c := by unfold Cone.InCone; omega
  have hg : 2 ≤ Cone.growth 1 m 1 := by unfold Cone.growth; grind
  rintro ⟨candidates,hcover⟩
  obtain ⟨n,hfinite,hext⟩ := ExtendedWeakPairs.cone_escapes_finite_core_and_exterior
    1 m 1 ⟨a,b,c⟩ (by decide) (by omega) (by decide) hcone hg
    (Or.inr (Or.inl ⟨rfl,rfl⟩)) candidates
  rcases hcover (Cone.repeatedWord n) with ⟨C,hC,p,hp⟩ | he
  · exact hfinite C hC p hp
  · exact hext he

theorem familyG_no_finite_core_exterior_cover (n : Int) (hn : 1 ≤ n) :
    ¬ ExtendedWeakPairs.FiniteCoreExteriorCover (familyG n) :=
  no_finite_core_exterior_cover _ _ _ _ (familyG_domain n hn)

end QuiverProofs.StripTriangles
