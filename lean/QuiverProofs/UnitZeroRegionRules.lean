import QuiverProofs.UnitZeroStrip
import QuiverProofs.RecursiveRegionSemantics

/-! Transport the complete N rule into any recursive region presentation.
The encoding hypotheses are exact matrix equalities, not mutation or cover
assumptions. They allow the N rule to be embedded into the combined grammar. -/
namespace QuiverProofs.UnitZeroRegionRules
open RecursiveRegions UnitZeroStrip TriangleRegions
universe u v

structure Encoding {R : Type u} (D : RegionData.{u,v} R) (r : R)
    (x : Int) (p : Parameters) where
  index : Nat → Fin 10 → D.Index r
  parentIndex : Fin 2 → Fin (D.parentCount r)
  state_eq : ∀ n i, D.state r (index n i) = strip x p n i
  parent_eq : ∀ j, D.parent r (parentIndex j) = UnitZeroStrip.parent x p j

theorem local_edges {R : Type u} (D : RegionData.{u,v} R) (r : R)
    (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (E : Encoding D r x p) (n : Nat) (i : Fin 10) (k : Fin 4) :
    LocalEdge D r (mutate (D.state r (E.index n i)) k) k := by
  rw [E.state_eq]
  rcases all_edges x p h n i k with ⟨n',i',f,heq⟩|⟨j,f,heq⟩|hf|hr
  · left
    rw [heq,←E.state_eq n' i']
    exact LocalAddress.framed (LocalAddress.node (E.index n' i') True.intro) f
  · left
    rw [heq,←E.parent_eq j]
    exact LocalAddress.framed (LocalAddress.parent (E.parentIndex j)) f
  · right; left; exact hf
  · right; right; left; exact hr

theorem local_triangle_descent {R : Type u} (D : RegionData.{u,v} R) (r : R)
    (x : Int) (p : Parameters) (h : Domain x p.u p.v p.w)
    (E : Encoding D r x p) (rank : D.Index r → Nat)
    (hrank : ∀ n i, rank (E.index n i)=descentRank n i)
    (n : Nat) (i : Fin 10) :
    ∃ k, Pendant.DeletionMA (D.state r (E.index n i)) k ∧
      LocalAddress D r (fun j => rank j < rank (E.index n i))
        (mutate (D.state r (E.index n i)) k) := by
  refine ⟨inward i,?_,?_⟩
  · rw [E.state_eq]
    exact deletionMA _ _ _ _ (orbit_domain x p h n) i
  · rw [E.state_eq]
    rcases inward_descent x p h n i with ⟨n',i',hr,heq⟩|⟨j,f,heq⟩
    · rw [heq,←E.state_eq n' i']
      apply LocalAddress.node (E.index n' i')
      simpa only [hrank] using hr
    · rw [heq,←E.parent_eq j]
      exact LocalAddress.framed (LocalAddress.parent (E.parentIndex j)) f

end QuiverProofs.UnitZeroRegionRules
