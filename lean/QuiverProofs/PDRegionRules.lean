import QuiverProofs.RecursiveRegionSemantics
import QuiverProofs.PendantSquare

/-! The exact two-orientation pendant square as a recursive region.
Both return parents are mandatory. The recursive child explicitly wires both
parents back to the displayed states; triangle descent returns to a parent. -/
namespace QuiverProofs.PDRegionRules
open RecursiveRegions TriangleRegions

structure Seed where
  c : Int
  d : Int
  x : Int
  y : Int
  domain : PendantSquare.Domain c d x y

def sign (i : Fin 2) : Int := if i=0 then 1 else -1

def state (r : Seed) (i : Fin 2) : Matrix 4 :=
  PendantSquare.state r.c r.d r.x r.y (sign i)

def parent (r : Seed) (i : Fin 2) : Matrix 4 := mutate (state r i) 1

theorem sign_valid (i : Fin 2) : PendantSquare.Sign (sign i) := by
  unfold sign PendantSquare.Sign
  split <;> simp

def data : RegionData Seed where
  Index := fun _ => Fin 2
  parentCount := fun _ => 2
  state := state
  parent := parent
  skew r i := ofSix_skew _ _ _ _ _ _
  parent_skew r i := mutation_preserves_skew _ _ (ofSix_skew _ _ _ _ _ _)
  cyclic r i := PendantSquare.cyclic r.c r.d r.x r.y (sign i) r.domain

def child (r : Seed) : Seed :=
  ⟨r.c,r.d,r.y,r.d*r.y-r.x,PendantSquare.child_domain r.c r.d r.x r.y r.domain⟩

def other (i : Fin 2) : Fin 2 := if i=0 then 1 else 0

theorem leaf (r : Seed) (i : Fin 2) : mutate (state r i) 0 = state r (other i) := by
  unfold state
  rw [PendantSquare.leaf]
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl|rfl <;> rfl

theorem child_frame (r : Seed) (i : Fin 2) :
    relabel (mutate (state r i) 2) PendantSquare.swap12 = state (child r) i :=
  PendantSquare.child_frame r.c r.d r.x r.y (sign i) r.domain

theorem child_entry (r : Seed) (i : Fin 2) :
    mutate (state r i) 2 = relabel (state (child r) i) PendantSquare.swap12.symm := by
  rw [←child_frame]
  exact (relabel_inverse _ _).symm

/-- Both child parents are actual framed current states, independently of
which orientation was entered. -/
theorem child_parent (r : Seed) (i : Fin 2) :
    parent (child r) i = relabel (state r i) PendantSquare.swap12 := by
  unfold parent
  rw [←child_frame,mutate_relabel]
  change relabel (mutate (mutate (state r i) 2) 2) PendantSquare.swap12 = _
  rw [mutation_involutive]

theorem edges (r : Seed) (i : Fin 2) (k : Fin 4) :
    LocalEdge data r (mutate (state r i) k) k := by
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hk with rfl|rfl|rfl|rfl
  · rw [leaf]
    exact Or.inl (LocalAddress.node (D:=data) (r:=r) (other i) trivial)
  · exact Or.inl (LocalAddress.parent (D:=data) (r:=r) i)
  · refine Or.inr (Or.inr (Or.inr ⟨child r,?_,?_⟩))
    · rw [child_entry]
      exact LocalAddress.framed (LocalAddress.node (D:=data) (r:=child r) i trivial)
        PendantSquare.swap12.symm
    · intro j
      change LocalAddress data r (fun _ => True) (parent (child r) j)
      rw [child_parent]
      exact LocalAddress.framed (LocalAddress.node (D:=data) (r:=r) j trivial)
        PendantSquare.swap12
  · exact Or.inr (Or.inr (Or.inl
      (PendantSquare.junction_isRoot r.c r.d r.x r.y (sign i) r.domain (sign_valid i))))

def rules : RegionRules data := ⟨edges⟩

theorem deletionMA (r : Seed) (i : Fin 2) : Pendant.DeletionMA (state r i) 1 := by
  obtain ⟨rank,hr⟩ := PendantSquare.return_deletion_acyclic
    r.c r.d r.x r.y (sign i) r.domain (sign_valid i)
  intro e he hp
  exact acyclic_is_mutationAcyclic _
    ⟨rank ∘ e,fun a b hab => hr (e a) (e b) (hp a) (hp b) hab⟩

/-- Every cyclic retained triangle descends through return 1 to a supplied
parent. No descent to a recursively attached child is assumed. -/
def triangleRules : TriangleRules data where
  rank _ _ := 0
  descent r i := Or.inr ⟨1,deletionMA r i,LocalAddress.parent (D:=data) (r:=r) i⟩

end QuiverProofs.PDRegionRules
