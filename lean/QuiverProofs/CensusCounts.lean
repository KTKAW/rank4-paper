import QuiverProofs.Census
import QuiverProofs.CensusConnections

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuiverProofs.Census

/-- The 15,625 base-five codes are an exact enumeration of labeled bounded
skew matrices: each input has exactly one code. -/
theorem bounded_labeled_unique_code (B : Matrix 4) (hskew : SkewSymmetric B)
    (hbound : BoundedTwo B) :
    ∃ n : Fin 15625, codeMatrix n.val = B ∧
      ∀ m : Fin 15625, codeMatrix m.val = B → m=n := by
  let n : Fin 15625 := ⟨matrixCode B,bounded_matrix_code_lt B hbound⟩
  have hn : codeMatrix n.val = B := bounded_matrix_decode B hskew hbound
  refine ⟨n,hn,?_⟩
  intro m hm
  exact codeMatrix_injective m n (hm.trans hn.symm)

def connectedRepresentative (i : Fin 667) : Matrix 4 :=
  connectionRepresentative ⟨i.val, by omega⟩

def disconnectedRepresentative (i : Fin 28) : Matrix 4 :=
  connectionRepresentative ⟨667+i.val, by omega⟩

theorem connected_representatives_connected (i : Fin 667) :
    ConnectedSupport (connectedRepresentative i) :=
  (connectivity_partition ⟨i.val, by omega⟩).mpr i.isLt

theorem disconnected_representatives_disconnected (i : Fin 28) :
    ¬ ConnectedSupport (disconnectedRepresentative i) := by
  intro h
  have hbad := (connectivity_partition ⟨667+i.val,by omega⟩).mp h
  change 667+i.val < 667 at hbad
  omega

theorem connection_representatives_pairwise_nonisomorphic
    (i j : Fin 695) (p : Relabeling 4)
    (h : relabel (connectionRepresentative i) p = connectionRepresentative j) : i=j := by
  have heq := representatives_pairwise_nonisomorphic
    ⟨connectionCodes.get i.val, connection_code_bounds i⟩
    ⟨connectionCodes.get j.val, connection_code_bounds j⟩ p h
  have hval := congrArg (fun k : Fin 695 => connectionInverse.get k.val) heq
  change connectionInverse.get (connectionCodes.get i.val) =
    connectionInverse.get (connectionCodes.get j.val) at hval
  rw [connection_inverse_left,connection_inverse_left] at hval
  exact Fin.ext hval

theorem connected_representatives_pairwise_nonisomorphic
    (i j : Fin 667) (p : Relabeling 4)
    (h : relabel (connectedRepresentative i) p = connectedRepresentative j) : i=j := by
  have heq := connection_representatives_pairwise_nonisomorphic
    ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ p h
  have hval : i.val = j.val := congrArg (fun z : Fin 695 => z.val) heq
  exact Fin.ext hval

theorem disconnected_representatives_pairwise_nonisomorphic
    (i j : Fin 28) (p : Relabeling 4)
    (h : relabel (disconnectedRepresentative i) p = disconnectedRepresentative j) : i=j := by
  have heq := connection_representatives_pairwise_nonisomorphic
    ⟨667+i.val,by omega⟩ ⟨667+j.val,by omega⟩ p h
  have hval : 667+i.val = 667+j.val := congrArg (fun z : Fin 695 => z.val) heq
  apply Fin.ext
  omega

theorem connection_representative_inverse (r : Fin 695) :
    connectionRepresentative ⟨connectionInverse.get r.val, connection_inverse_bounds r⟩ =
      representative r := by
  change rawRepresentative (connectionCodes.get (connectionInverse.get r.val)) = rawRepresentative r.val
  rw [connection_inverse_right]

theorem representative_connectivity_index (r : Fin 695) :
    ConnectedSupport (representative r) ↔ connectionInverse.get r.val < 667 := by
  have h := connectivity_partition
    ⟨connectionInverse.get r.val,connection_inverse_bounds r⟩
  rw [connection_representative_inverse] at h
  exact h

theorem connected_representative_count :
    ((List.finRange 695).filter (fun r => decide (ConnectedSupport (representative r)))).length = 667 := by
  simp only [representative_connectivity_index]
  decide

theorem disconnected_representative_count :
    ((List.finRange 695).filter (fun r => !decide (ConnectedSupport (representative r)))).length = 28 := by
  simp only [representative_connectivity_index]
  decide

theorem ma_connectivity_index (i : Fin 561) :
    ConnectedSupport (maRepresentative i) ↔ connectionInverse.get (maRepCodes.get i.val) < 667 :=
  representative_connectivity_index ⟨maRepCodes.get i.val,ma_source_indices i⟩

/-- Counts of actual proved MA representatives, not imported classification labels. -/
theorem connected_ma_representative_count :
    ((List.finRange 561).filter (fun i => decide (ConnectedSupport (maRepresentative i)))).length = 534 := by
  simp only [ma_connectivity_index]
  decide

theorem disconnected_ma_representative_count :
    ((List.finRange 561).filter (fun i => !decide (ConnectedSupport (maRepresentative i)))).length = 27 := by
  simp only [ma_connectivity_index]
  decide

/-- Exhaustive connected census, with exactly 667 pairwise nonisomorphic
representatives. No mutation classification assumption enters this statement. -/
theorem connected_bounded_census (B : Matrix 4) (hskew : SkewSymmetric B)
    (hbound : BoundedTwo B) (hconn : ConnectedSupport B) :
    ∃ (i : Fin 667) (p : Relabeling 4), relabel (connectedRepresentative i) p = B := by
  obtain ⟨r,p,hp⟩ := all_bounded_quivers_covered B hskew hbound
  let t : Fin 695 := ⟨connectionInverse.get r.val, connection_inverse_bounds r⟩
  have ht : connectionRepresentative t = representative r := connection_representative_inverse r
  have hct : ConnectedSupport (connectionRepresentative t) := by
    rw [ht]
    apply (connected_relabel_iff _ (permutation p)).mp
    rw [hp]
    exact hconn
  have hsmall : t.val < 667 := (connectivity_partition t).mp hct
  refine ⟨⟨t.val,hsmall⟩, permutation p, ?_⟩
  change relabel (connectionRepresentative t) (permutation p) = B
  rw [ht]
  exact hp

/-- Exhaustive disconnected census, with exactly 28 pairwise nonisomorphic
representatives. -/
theorem disconnected_bounded_census (B : Matrix 4) (hskew : SkewSymmetric B)
    (hbound : BoundedTwo B) (hconn : ¬ ConnectedSupport B) :
    ∃ (i : Fin 28) (p : Relabeling 4), relabel (disconnectedRepresentative i) p = B := by
  obtain ⟨r,p,hp⟩ := all_bounded_quivers_covered B hskew hbound
  let t : Fin 695 := ⟨connectionInverse.get r.val, connection_inverse_bounds r⟩
  have ht : connectionRepresentative t = representative r := connection_representative_inverse r
  have hct : ¬ ConnectedSupport (connectionRepresentative t) := by
    intro hc
    rw [ht] at hc
    have hh := (connected_relabel_iff _ (permutation p)).mpr hc
    rw [hp] at hh
    exact hconn hh
  have hnot : ¬ t.val < 667 := fun hlt => hct ((connectivity_partition t).mpr hlt)
  have hlarge : 667 ≤ t.val := by omega
  let d : Fin 28 := ⟨t.val-667,by omega⟩
  have hindex : (⟨667+d.val,by omega⟩ : Fin 695) = t := by
    apply Fin.ext
    dsimp [d]
    omega
  refine ⟨d, permutation p, ?_⟩
  unfold disconnectedRepresentative
  rw [hindex,ht]
  exact hp

end QuiverProofs.Census
