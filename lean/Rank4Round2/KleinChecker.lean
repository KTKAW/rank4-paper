import Rank4Round2.KleinClosure
import QuiverProofs.Census

/-! Computable recognition of the accepted six-parameter Klein region in
all twenty-four vertex frames and both arrow orientations. A successful
recognition proves original NMA unconditionally; false leaves the input open.
-/
namespace Rank4Round2.KleinChecker
open QuiverProofs KleinRegion

def recover (Q : Matrix 4) : Parameters :=
  let a := Q 0 1
  let c := -Q 0 3
  let d := Q 1 2
  let E := -Q 1 3+a*c
  ⟨a,c,d,Q 0 2*c+d*E-Q 2 3,E,Q 0 2+a*d⟩

theorem recover_node (Q : Matrix 4) (hs : SkewSymmetric Q) :
    node (recover Q) 0=Q := by
  have hb : b (recover Q)=Q 0 2 := by unfold b recover; dsimp only; ring
  have he : e (recover Q)= -Q 1 3 := by unfold e recover; dsimp only; ring
  have hf : f (recover Q)=Q 2 3 := by unfold f b recover; dsimp only; ring
  change ofSix (Q 0 1) (b (recover Q)) (-(-Q 0 3)) (Q 1 2)
    (-(e (recover Q))) (f (recover Q))=Q
  rw [hb,he,hf]
  simp only [Int.neg_neg]
  exact ofSix_reconstruct Q hs

def recognized (Q : Matrix 4) : Prop :=
  ∃ i : Fin 24, Domain (recover (relabel Q (Census.permutation i))) ∨
    Domain (recover (reverse (relabel Q (Census.permutation i))))

instance recognizedDecidable (Q : Matrix 4) : Decidable (recognized Q) := by
  unfold recognized Domain
  infer_instance

def check (Q : Matrix 4) : Bool := decide (recognized Q)

theorem canonical_NMA (Q : Matrix 4) (hs : SkewSymmetric Q)
    (hd : Domain (recover Q)) : ¬MutationAcyclic Q := by
  have h := core_NMA (recover Q) hd
  rwa [recover_node Q hs] at h

theorem check_sound (Q : Matrix 4) (hs : SkewSymmetric Q) (h : check Q=true) :
    ¬MutationAcyclic Q := by
  have hr : recognized Q := of_decide_eq_true h
  obtain ⟨i,hi⟩ := hr
  let p := Census.permutation i
  have hs' : SkewSymmetric (relabel Q p) := relabel_skew Q p hs
  rcases hi with hD|hD
  · have hn := canonical_NMA (relabel Q p) hs' hD
    exact fun hma => hn ((MA_relabel_iff Q p).mpr hma)
  · have hn := canonical_NMA (reverse (relabel Q p)) (reverse_skew _ hs') hD
    exact fun hma => hn ((MA_reverse_iff _ hs').mpr ((MA_relabel_iff Q p).mpr hma))

#eval check (ofSix 2 2 (-2) 2 (-2) 14)
#eval check (ofSix 2 1 (-2) 2 (-2) 12)
#print axioms recover
#print axioms check
#print axioms check_sound
end Rank4Round2.KleinChecker
