import QuiverProofs.CensusCore

namespace QuiverProofs.Census

def side (a b c d : Bool) (i : Fin 4) : Bool :=
  match i.val with | 0 => a | 1 => b | 2 => c | _ => d

def RespectsEdges (B : Matrix 4) (s : Fin 4 → Bool) : Prop :=
  ∀ i j, B i j ≠ 0 → s i = s j

instance (B : Matrix 4) (s : Fin 4 → Bool) : Decidable (RespectsEdges B s) := by
  unfold RespectsEdges; infer_instance

/-- Connectivity by cuts: every Boolean coloring constant along edges is
constant on all vertices. This is the no-nontrivial-disconnected-cut definition. -/
def ConnectedSupport (B : Matrix 4) : Prop :=
  ∀ a b c d : Bool, RespectsEdges B (side a b c d) → a=b ∧ b=c ∧ c=d

instance (B : Matrix 4) : Decidable (ConnectedSupport B) := by
  unfold ConnectedSupport; infer_instance

private theorem cases4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem connected_iff_all_colorings (B : Matrix 4) :
    ConnectedSupport B ↔ ∀ s : Fin 4 → Bool, RespectsEdges B s → ∀ i j, s i = s j := by
  constructor
  · intro h s hs
    have heq : side (s 0) (s 1) (s 2) (s 3) = s := by
      funext i
      rcases cases4 i with rfl | rfl | rfl | rfl <;> rfl
    have hh := h (s 0) (s 1) (s 2) (s 3)
    rw [heq] at hh
    obtain ⟨h01,h12,h23⟩ := hh hs
    intro i j
    rcases cases4 i with rfl | rfl | rfl | rfl <;>
      rcases cases4 j with rfl | rfl | rfl | rfl <;> simp_all
  · intro h a b c d hs
    have hh := h (side a b c d) hs
    exact ⟨hh 0 1, hh 1 2, hh 2 3⟩

theorem connected_relabel (B : Matrix 4) (p : Relabeling 4)
    (hB : ConnectedSupport B) : ConnectedSupport (relabel B p) := by
  apply (connected_iff_all_colorings _).mpr
  intro s hs
  have hOld : RespectsEdges B (s ∘ p.invFun) := by
    intro i j hij
    have hEdge : relabel B p (p.invFun i) (p.invFun j) ≠ 0 := by
      simpa only [relabel,p.right_inv] using hij
    exact hs _ _ hEdge
  have hh := (connected_iff_all_colorings B).mp hB (s ∘ p.invFun) hOld
  intro i j
  simpa only [Function.comp_apply,p.left_inv] using hh (p.toFun i) (p.toFun j)

theorem connected_relabel_iff (B : Matrix 4) (p : Relabeling 4) :
    ConnectedSupport (relabel B p) ↔ ConnectedSupport B := by
  constructor
  · intro h
    have hh := connected_relabel (relabel B p) p.symm h
    simpa only [relabel_inverse] using hh
  · exact connected_relabel B p

end QuiverProofs.Census
