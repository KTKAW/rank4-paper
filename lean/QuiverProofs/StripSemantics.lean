import QuiverProofs.GenericStripBoundaries
import QuiverProofs.RegionCells

/-! An infinite strip with its three base interfaces supplied explicitly.
The induction here covers every finite mutation word, including all fork and
unit-prefork excursions and all label frames and simultaneous reversals. -/
namespace QuiverProofs.StripSemantics
open GenericStrip Forks
open Regions (IsRoot)

inductive Core (m : Int) (s : Cone.State) (base : Matrix 4 → Prop) : Matrix 4 → Prop
  | base {B : Matrix 4} : base B → Core m s base B
  | strip (n : Nat) (i : Fin 6) :
      Core m s base (phase m (orbit m s n).A (orbit m s n).H (orbit m s n).Z i)
  | framed {B : Matrix 4} : Core m s base B → (p : Relabeling 4) →
      Core m s base (relabel B p)
  | reversed {B : Matrix 4} : Core m s base B → Core m s base (reverse B)

def Exit (core : Matrix 4 → Prop) (B : Matrix 4) (k : Fin 4) : Prop :=
  core (mutate B k) ∨ IsFork (mutate B k) k ∨ IsRoot (mutate B k) k

theorem core_skew (m : Int) (s : Cone.State) (base : Matrix 4 → Prop)
    (hb : ∀ B, base B → SkewSymmetric B) {B : Matrix 4} (h : Core m s base B) :
    SkewSymmetric B := by
  induction h with
  | base h => exact hb _ h
  | strip n i => exact phase_skew _ _ _ _ i
  | framed _ p ih => exact relabel_skew _ p ih
  | reversed _ ih => exact reverse_skew _ ih

theorem core_cyclic (m : Int) (s : Cone.State) (base : Matrix 4 → Prop)
    (hd : GenericStrip.Domain m s.A s.H s.Z)
    (hs : ∀ B, base B → SkewSymmetric B) (hb : ∀ B, base B → ¬ Acyclic B)
    {B : Matrix 4} (h : Core m s base B) : ¬ Acyclic B := by
  induction h with
  | base h => exact hb _ h
  | strip n i => exact phase_cyclic _ _ _ _ (orbit_domain m s hd n) i
  | framed _ p ih => exact fun ha => ih ((acyclic_relabel_iff _ p).mp ha)
  | reversed h ih =>
    exact fun ha => ih ((acyclic_reverse_iff _ (core_skew m s base hs h)).mp ha)

theorem strip_edges (m : Int) (s : Cone.State) (base : Matrix 4 → Prop)
    (hd : GenericStrip.Domain m s.A s.H s.Z)
    (hR1 : Core m s base (mutate (root m s.A s.H s.Z) 1))
    (hR2 : Core m s base (mutate (root m s.A s.H s.Z) 2))
    (hQ0 : Core m s base (mutate (phaseQ m s.A s.H s.Z) 0))
    (n : Nat) (i : Fin 6) (k : Fin 4) :
    Exit (Core m s base) (phase m (orbit m s n).A (orbit m s n).H (orbit m s n).Z i) k := by
  have h := orbit_domain m s hd n
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hk with rfl|rfl|rfl|rfl
  · left; rw [show phase m _ _ _ 0 = root m _ _ _ from rfl, root_zero _ _ _ _ h]
    exact Core.strip n 1
  · left
    cases n with
    | zero => exact hR1
    | succ n =>
      change Core m s base (mutate (root m (nextA _ _ _ _) (nextB _ _ _) (nextC _ _ _ _)) 1)
      rw [next_root_one _ _ _ _ (orbit_domain m s hd n)]
      exact Core.framed (Core.strip n 4) Regions.frame0213
  · left
    cases n with
    | zero => exact hR2
    | succ n =>
      change Core m s base (mutate (root m (nextA _ _ _ _) (nextB _ _ _) (nextC _ _ _ _)) 2)
      rw [next_root_two _ _ _ _ (orbit_domain m s hd n)]
      exact Core.strip n 2
  · exact Or.inr (Or.inr (GenericStripBoundaries.root_three _ _ _ _ h))
  · left; rw [show phase m _ _ _ 1 = phaseP m _ _ _ from rfl, P_zero _ _ _ _ h]
    exact Core.strip n 0
  · left; rw [show phase m _ _ _ 1 = phaseP m _ _ _ from rfl, P_one _ _ _ _ h]
    exact Core.strip n 2
  · left; rw [show phase m _ _ _ 1 = phaseP m _ _ _ from rfl, P_two _ _ _ _ h]
    exact Core.strip n 3
  · exact Or.inr (Or.inr (GenericStripBoundaries.P_three _ _ _ _ h))
  · left
    cases n with
    | zero => exact hQ0
    | succ n =>
      change Core m s base (mutate (phaseQ m (nextA _ _ _ _) (nextB _ _ _) (nextC _ _ _ _)) 0)
      rw [next_Q_zero _ _ _ _ (orbit_domain m s hd n)]
      exact Core.framed (Core.strip n 5) Regions.frame1203.symm
  · left; rw [show phase m _ _ _ 2 = phaseQ m _ _ _ from rfl, Q_one _ _ _ _ h]
    exact Core.strip n 1
  · left; rw [show phase m _ _ _ 2 = phaseQ m _ _ _ from rfl, Q_two _ _ _ _ h]
    exact Core.strip (n+1) 0
  · exact Or.inr (Or.inl (GenericStripBoundaries.Q_three _ _ _ _ h))
  · exact Or.inr (Or.inl (GenericStripBoundaries.S_zero _ _ _ _ h))
  · left; rw [show phase m _ _ _ 3 = phaseS m _ _ _ from rfl, S_one _ _ _ _ h]
    exact Core.strip n 4
  · left; rw [show phase m _ _ _ 3 = phaseS m _ _ _ from rfl, S_two _ _ _ _ h]
    exact Core.strip n 1
  · exact Or.inr (Or.inl (GenericStripBoundaries.S_three _ _ _ _ h))
  · left; rw [show phase m _ _ _ 4 = phaseT m _ _ _ from rfl, T_zero _ _ _ _ h]
    exact Core.strip n 5
  · left; rw [show phase m _ _ _ 4 = phaseT m _ _ _ from rfl, T_one _ _ _ _ h]
    exact Core.strip n 3
  · left
    rw [← relabel_inverse (mutate (phase m _ _ _ 4) 2) Regions.frame0213]
    rw [show phase m _ _ _ 4 = phaseT m _ _ _ from rfl, T_two _ _ _ _ h]
    exact Core.framed (Core.strip (n+1) 0) Regions.frame0213.symm
  · exact Or.inr (Or.inr (GenericStripBoundaries.T_three _ _ _ _ h))
  · left; rw [show phase m _ _ _ 5 = phaseV m _ _ _ from rfl, V_zero _ _ _ _ h]
    exact Core.strip n 4
  · exact Or.inr (Or.inl (GenericStripBoundaries.V_one _ _ _ _ h))
  · left
    rw [← relabel_inverse (mutate (phase m _ _ _ 5) 2) Regions.frame1203.symm]
    rw [show phase m _ _ _ 5 = phaseV m _ _ _ from rfl, V_two _ _ _ _ h]
    exact Core.framed (Core.strip (n+1) 2) Regions.frame1203.symm.symm
  · exact Or.inr (Or.inr (GenericStripBoundaries.V_three _ _ _ _ h))

theorem core_edges (m : Int) (s : Cone.State) (base : Matrix 4 → Prop)
    (hd : GenericStrip.Domain m s.A s.H s.Z)
    (hb : ∀ B, base B → ∀ k, Exit (Core m s base) B k)
    (hR1 : Core m s base (mutate (root m s.A s.H s.Z) 1))
    (hR2 : Core m s base (mutate (root m s.A s.H s.Z) 2))
    (hQ0 : Core m s base (mutate (phaseQ m s.A s.H s.Z) 0))
    {B : Matrix 4} (h : Core m s base B) (k : Fin 4) : Exit (Core m s base) B k := by
  induction h generalizing k with
  | base h => exact hb _ h k
  | strip n i => exact strip_edges m s base hd hR1 hR2 hQ0 n i k
  | @framed B h p ih =>
    rcases ih (p.toFun k) with hc | hf | hr
    · left; rw [mutate_relabel]; exact Core.framed hc p
    · right; left; rw [mutate_relabel]
      simpa only [p.left_inv] using IsFork.relabelled hf p
    · right; right; rw [mutate_relabel]
      simpa only [p.left_inv] using IsRoot.relabelled hr p
  | reversed h ih =>
    rcases ih k with hc | hf | hr
    · left; rw [mutate_reverse]; exact Core.reversed hc
    · right; left; rw [mutate_reverse]; exact IsFork.reversed hf
    · right; right; rw [mutate_reverse]; exact IsRoot.reversed hr

theorem core_NMA (m : Int) (s : Cone.State) (base : Matrix 4 → Prop)
    (hd : GenericStrip.Domain m s.A s.H s.Z)
    (hs : ∀ B, base B → SkewSymmetric B) (hc : ∀ B, base B → ¬ Acyclic B)
    (he : ∀ B, base B → ∀ k, Exit (Core m s base) B k)
    (hR1 : Core m s base (mutate (root m s.A s.H s.Z) 1))
    (hR2 : Core m s base (mutate (root m s.A s.H s.Z) 2))
    (hQ0 : Core m s base (mutate (phaseQ m s.A s.H s.Z) 0))
    (B : Matrix 4) (hB : Core m s base B) : ¬ MutationAcyclic B := by
  apply RegionSemantics.region_NMA RegionCells.root_cells_exist (Core m s base)
  · exact fun B h => core_skew m s base hs h
  · exact fun B h => core_cyclic m s base hd hs hc h
  · exact fun B h k => core_edges m s base hd he hR1 hR2 hQ0 h k
  · exact hB

end QuiverProofs.StripSemantics
