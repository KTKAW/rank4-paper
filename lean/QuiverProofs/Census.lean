import QuiverProofs.CensusDistinct
import QuiverProofs.CensusChunks

namespace QuiverProofs.Census

/-- Every encoded labeled tuple is explicitly a relabeling of a supplied
representative. The table is checked across all 15,625 cases in CensusChunks. -/
theorem codeMatrix_covered (n : Fin 15625) :
    ∃ (r : Fin 695) (p : Fin 24), relabel (representative r) (permutation p) = codeMatrix n.val := by
  obtain ⟨hbound, heq⟩ := encoded_census n
  let w := witnessCodes.get n.val
  have hw : w < 695*24 := hbound
  refine ⟨⟨w/24, by omega⟩, ⟨w%24, by omega⟩, ?_⟩
  funext i j
  exact heq i j

/-- Exhaustive coverage of every integral skew-symmetric four-by-four matrix
whose arrow multiplicities are at most two. No classification labels are used. -/
theorem all_bounded_quivers_covered (B : Matrix 4) (hskew : SkewSymmetric B)
    (h : BoundedTwo B) :
    ∃ (r : Fin 695) (p : Fin 24), relabel (representative r) (permutation p) = B := by
  obtain ⟨r,p,heq⟩ := codeMatrix_covered ⟨matrixCode B, bounded_matrix_code_lt B h⟩
  exact ⟨r,p,heq.trans (bounded_matrix_decode B hskew h)⟩

/-- The census gives exactly one representative index for every bounded quiver.
Together with `representatives_pairwise_nonisomorphic`, this states the exact
695-class census without using any source MA/NMA labels. -/
theorem bounded_quiver_unique_representative (B : Matrix 4)
    (hskew : SkewSymmetric B) (hbound : BoundedTwo B) :
    ∃ i : Fin 695,
      (∃ p : Relabeling 4, relabel (representative i) p = B) ∧
      ∀ (j : Fin 695) (q : Relabeling 4), relabel (representative j) q = B → j=i := by
  obtain ⟨i,p,hp⟩ := all_bounded_quivers_covered B hskew hbound
  refine ⟨i, ⟨permutation p,hp⟩, ?_⟩
  intro j q hq
  apply representatives_pairwise_nonisomorphic j i (compose q (permutation p).symm)
  have hcomp : relabel (representative j) (compose q (permutation p).symm) =
      relabel (relabel (representative j) q) (permutation p).symm := rfl
  rw [hcomp,hq,← hp]
  exact relabel_inverse _ _

end QuiverProofs.Census
