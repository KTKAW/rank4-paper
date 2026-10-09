import QuiverProofs.RecursiveRegionSemantics
import QuiverProofs.StripTriangles

namespace QuiverProofs.GenericRegionAdapter
open RecursiveRegions GenericStrip TriangleRegions

structure Seed where
  m : Int
  s : Cone.State
  domain : Domain m s.A s.H s.Z

def state (r : Seed) (i : Nat × Fin 6) : Matrix 4 :=
  phase r.m (orbit r.m r.s i.1).A (orbit r.m r.s i.1).H (orbit r.m r.s i.1).Z i.2

def parent (r : Seed) (p : Fin 3) : Matrix 4 :=
  if p = 0 then mutate (root r.m r.s.A r.s.H r.s.Z) 1
  else if p = 1 then mutate (root r.m r.s.A r.s.H r.s.Z) 2
  else mutate (phaseQ r.m r.s.A r.s.H r.s.Z) 0

def data : RegionData Seed where
  Index := fun _ => Nat × Fin 6
  parentCount := fun _ => 3
  state := state
  parent := parent
  skew r i := phase_skew _ _ _ _ _
  parent_skew r p := by
    unfold parent
    split
    · exact mutation_preserves_skew _ _ (phase_skew _ _ _ _ 0)
    · split
      · exact mutation_preserves_skew _ _ (phase_skew _ _ _ _ 0)
      · exact mutation_preserves_skew _ _ (phase_skew _ _ _ _ 2)
  cyclic r i := phase_cyclic _ _ _ _ (orbit_domain r.m r.s r.domain i.1) i.2

theorem address_of_core (r : Seed) {B : Matrix 4}
    (h : StripSemantics.Core r.m r.s (fun B => ∃ p, parent r p = B) B) :
    LocalAddress data r (fun _ => True) B := by
  induction h with
  | base h =>
    obtain ⟨p,rfl⟩ := h
    exact LocalAddress.parent (D := data) (r := r) p
  | strip n i => exact LocalAddress.node (D := data) (r := r) (n,i) trivial
  | framed _ p ih => exact LocalAddress.framed ih p
  | reversed _ ih => exact LocalAddress.reversed ih

theorem edges (r : Seed) (i : Nat × Fin 6) (k : Fin 4) :
    LocalEdge data r (mutate (state r i) k) k := by
  have he := StripSemantics.strip_edges r.m r.s (fun B => ∃ p, parent r p = B)
    r.domain
    (StripSemantics.Core.base ⟨0,by simp [parent]⟩)
    (StripSemantics.Core.base ⟨1,by simp [parent]⟩)
    (StripSemantics.Core.base ⟨2,by simp [parent]⟩) i.1 i.2 k
  rcases he with hc | hf | hr
  · exact Or.inl (address_of_core r hc)
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr (Or.inl hr))

def rules : RegionRules data := ⟨edges⟩

def level (i : Fin 6) : Nat := match i.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 2 | 4 => 3 | _ => 4

def rank (i : Nat × Fin 6) : Nat := 4 * i.1 + level i.2

theorem deletionMA (r : Seed) (i : Nat × Fin 6) :
    Pendant.DeletionMA (state r i) (StripTriangles.inward i.2) := by
  obtain ⟨d,hd⟩ := StripTriangles.phase_deletion _ _ _ _
    (orbit_domain r.m r.s r.domain i.1) i.2
  intro e he hp
  exact acyclic_is_mutationAcyclic _ ⟨d ∘ e,fun a b hab => hd _ _ (hp a) (hp b) hab⟩

theorem descent (r : Seed) (i : Nat × Fin 6) :
    LocalAddress data r (fun j => rank j < rank i)
      (mutate (state r i) (StripTriangles.inward i.2)) := by
  obtain ⟨n,i⟩ := i
  have hd := orbit_domain r.m r.s r.domain n
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · cases n with
    | zero => exact LocalAddress.parent (D := data) (r := r) (1 : Fin 3)
    | succ n =>
      change LocalAddress data r _
        (mutate (root r.m (nextA _ _ _ _) (nextB _ _ _) (nextC _ _ _ _)) 2)
      rw [next_root_two _ _ _ _ (orbit_domain r.m r.s r.domain n)]
      exact LocalAddress.node (D := data) (r := r) (n,2) (by simp [rank,level]; omega)
  · change LocalAddress data r _ (mutate (phaseP _ _ _ _) 0)
    rw [P_zero _ _ _ _ hd]
    exact LocalAddress.node (D := data) (r := r) (n,0) (by simp [rank,level])
  · change LocalAddress data r _ (mutate (phaseQ _ _ _ _) 1)
    rw [Q_one _ _ _ _ hd]
    exact LocalAddress.node (D := data) (r := r) (n,1) (by simp [rank,level])
  · change LocalAddress data r _ (mutate (phaseS _ _ _ _) 2)
    rw [S_two _ _ _ _ hd]
    exact LocalAddress.node (D := data) (r := r) (n,1) (by simp [rank,level])
  · change LocalAddress data r _ (mutate (phaseT _ _ _ _) 1)
    rw [T_one _ _ _ _ hd]
    exact LocalAddress.node (D := data) (r := r) (n,3) (by simp [rank,level])
  · change LocalAddress data r _ (mutate (phaseV _ _ _ _) 0)
    rw [V_zero _ _ _ _ hd]
    exact LocalAddress.node (D := data) (r := r) (n,4) (by simp [rank,level])

def triangleRules : TriangleRules data where
  rank _ := rank
  descent r i := Or.inr ⟨StripTriangles.inward i.2, deletionMA r i, descent r i⟩

end QuiverProofs.GenericRegionAdapter
