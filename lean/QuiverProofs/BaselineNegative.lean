import QuiverProofs.Box
import QuiverProofs.Disconnected
import QuiverProofs.FiniteOrbit
import QuiverProofs.ResidualFamily
import QuiverProofs.Symmetry

/- Generated bridge obligations. Source labels are never proof assumptions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QuiverProofs.BaselineNegative

def perm0 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),by decide,by decide⟩

def perm5 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),by decide,by decide⟩

def perm7 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),by decide,by decide⟩

/-- Exact baseline input from sequel_research/certificates/q023.json. -/
theorem nma_q023 : ¬ MutationAcyclic (ofSix (-2) (-2) (-2) (-1) (1) (-1)) := by
  have hn : ¬ MutationAcyclic (ofSix (-2) (-2) (-2) (-1) (1) (-1)) := ResidualFamily.residual_three_parameter_NMA 2 2 2 (by decide) (by decide) (by decide)
  have he : relabel (ofSix (-2) (-2) (-2) (-1) (1) (-1)) perm0 = applyWord (ofSix (-2) (-2) (-2) (-1) (1) (-1)) [] := by
    funext i j
    exact (show ∀ i j : Fin 4, relabel (ofSix (-2) (-2) (-2) (-1) (1) (-1)) perm0 i j = applyWord (ofSix (-2) (-2) (-2) (-1) (1) (-1)) [] i j from by decide) i j
  intro hm
  have hw := (mutationAcyclic_word_iff (ofSix (-2) (-2) (-2) (-1) (1) (-1)) []).mpr hm
  rw [← he] at hw
  have hr := (MA_relabel_iff (ofSix (-2) (-2) (-2) (-1) (1) (-1)) perm0).mp hw
  exact hn hr

/-- Exact baseline input from sequel_research/certificates/q497.json. -/
theorem nma_q497 : ¬ MutationAcyclic (ofSix (-2) (-1) (1) (2) (2) (-1)) := by
  have hn : ¬ MutationAcyclic (ofSix (-2) (-2) (-2) (-1) (1) (-1)) := ResidualFamily.residual_three_parameter_NMA 2 2 2 (by decide) (by decide) (by decide)
  have he : relabel (reverse (ofSix (-2) (-2) (-2) (-1) (1) (-1))) perm7 = applyWord (ofSix (-2) (-1) (1) (2) (2) (-1)) [] := by
    funext i j
    exact (show ∀ i j : Fin 4, relabel (reverse (ofSix (-2) (-2) (-2) (-1) (1) (-1))) perm7 i j = applyWord (ofSix (-2) (-1) (1) (2) (2) (-1)) [] i j from by decide) i j
  intro hm
  have hw := (mutationAcyclic_word_iff (ofSix (-2) (-1) (1) (2) (2) (-1)) []).mpr hm
  rw [← he] at hw
  have hr := (MA_relabel_iff (reverse (ofSix (-2) (-2) (-2) (-1) (1) (-1))) perm7).mp hw
  exact hn ((MA_reverse_iff (ofSix (-2) (-2) (-2) (-1) (1) (-1)) (ofSix_skew _ _ _ _ _ _)).mp hr)

/-- Exact baseline input from sequel_research/certificates/q608.json. -/
theorem nma_q608 : ¬ MutationAcyclic (ofSix (-2) (0) (2) (-2) (0) (-2)) := by
  have hn : ¬ MutationAcyclic (ofSix (2) (0) (-2) (2) (0) (2)) := Box.box_NMA 2 2 (by decide) (by decide)
  have he : relabel (ofSix (2) (0) (-2) (2) (0) (2)) perm5 = applyWord (ofSix (-2) (0) (2) (-2) (0) (-2)) [] := by
    funext i j
    exact (show ∀ i j : Fin 4, relabel (ofSix (2) (0) (-2) (2) (0) (2)) perm5 i j = applyWord (ofSix (-2) (0) (2) (-2) (0) (-2)) [] i j from by decide) i j
  intro hm
  have hw := (mutationAcyclic_word_iff (ofSix (-2) (0) (2) (-2) (0) (-2)) []).mpr hm
  rw [← he] at hw
  have hr := (MA_relabel_iff (ofSix (2) (0) (-2) (2) (0) (2)) perm5).mp hw
  exact hn hr

/-- Exact baseline input from sequel_research/certificates/q617.json. -/
theorem nma_q617 : ¬ MutationAcyclic (ofSix (-2) (1) (1) (-1) (-1) (-1)) := by
  have hn : ¬ MutationAcyclic (ofSix (-2) (1) (1) (-1) (-1) (-1)) := FiniteOrbit.nma_q617
  have he : relabel (ofSix (-2) (1) (1) (-1) (-1) (-1)) perm0 = applyWord (ofSix (-2) (1) (1) (-1) (-1) (-1)) [] := by
    funext i j
    exact (show ∀ i j : Fin 4, relabel (ofSix (-2) (1) (1) (-1) (-1) (-1)) perm0 i j = applyWord (ofSix (-2) (1) (1) (-1) (-1) (-1)) [] i j from by decide) i j
  intro hm
  have hw := (mutationAcyclic_word_iff (ofSix (-2) (1) (1) (-1) (-1) (-1)) []).mpr hm
  rw [← he] at hw
  have hr := (MA_relabel_iff (ofSix (-2) (1) (1) (-1) (-1) (-1)) perm0).mp hw
  exact hn hr

/-- Exact baseline input from sequel_research/certificates/qd019.json. -/
theorem nma_qd019 : ¬ MutationAcyclic (ofSix (-2) (0) (2) (0) (-2) (0)) := by
  have hn : ¬ MutationAcyclic (ofSix (-2) (0) (2) (0) (-2) (0)) := QuiverProofs.nma_qd019
  have he : relabel (ofSix (-2) (0) (2) (0) (-2) (0)) perm0 = applyWord (ofSix (-2) (0) (2) (0) (-2) (0)) [] := by
    funext i j
    exact (show ∀ i j : Fin 4, relabel (ofSix (-2) (0) (2) (0) (-2) (0)) perm0 i j = applyWord (ofSix (-2) (0) (2) (0) (-2) (0)) [] i j from by decide) i j
  intro hm
  have hw := (mutationAcyclic_word_iff (ofSix (-2) (0) (2) (0) (-2) (0)) []).mpr hm
  rw [← he] at hw
  have hr := (MA_relabel_iff (ofSix (-2) (0) (2) (0) (-2) (0)) perm0).mp hw
  exact hn hr

end QuiverProofs.BaselineNegative
