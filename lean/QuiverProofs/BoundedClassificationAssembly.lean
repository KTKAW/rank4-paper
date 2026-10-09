import QuiverProofs.CensusCounts

namespace QuiverProofs.BoundedClassification
open Census

def ShortBounded (B : Matrix 4) : Prop :=
  ∃ w : List (Fin 4), w.length ≤ 3 ∧ BoundedRun B w ∧ Acyclic (applyWord B w)

theorem bounded_relabel (B : Matrix 4) (p : Relabeling 4) (h : BoundedTwo B) :
    BoundedTwo (relabel B p) := fun i j => h (p.toFun i) (p.toFun j)

theorem boundedRun_relabel (B : Matrix 4) (p : Relabeling 4) (w : List (Fin 4))
    (h : BoundedRun B w) : BoundedRun (relabel B p) (w.map p.invFun) := by
  induction w generalizing B with
  | nil => exact bounded_relabel B p h
  | cons k ks ih =>
    refine ⟨bounded_relabel B p h.1,?_⟩
    simpa only [mutate_relabel,p.right_inv] using ih (mutate B k) h.2

theorem shortBounded_relabel (B : Matrix 4) (p : Relabeling 4) (h : ShortBounded B) :
    ShortBounded (relabel B p) := by
  obtain ⟨w,hw,hb,ha⟩ := h
  refine ⟨w.map p.invFun,by simpa using hw,boundedRun_relabel B p w hb,?_⟩
  rw [word_relabel,List.map_map]
  have hm : List.map (p.toFun ∘ p.invFun) w = w := by
    have hf : p.toFun ∘ p.invFun = id := by funext x; exact p.right_inv x
    rw [hf,List.map_id]
  rw [hm]
  exact (acyclic_relabel_iff (applyWord B w) p).mpr ha

/-- The full bounded short-witness equivalence, once each MA census
representative is identified among the561 already checked positive inputs.
The premise is discharged by the complete negative proof table. -/
theorem bounded_classification_of_table
    (complete : ∀ r : Fin 695, MutationAcyclic (representative r) →
      ∃ i : Fin 561, representative r = maRepresentative i)
    (B : Matrix 4) (hs : SkewSymmetric B) (hb : BoundedTwo B) :
    MutationAcyclic B ↔ ShortBounded B := by
  constructor
  · intro hma
    obtain ⟨r,p,hp⟩ := all_bounded_quivers_covered B hs hb
    have hr : MutationAcyclic (representative r) := by
      apply (MA_relabel_iff _ (permutation p)).mp
      rwa [hp]
    obtain ⟨i,hi⟩ := complete r hr
    rw [←hp,hi]
    exact shortBounded_relabel _ (permutation p) (all_ma_short_bounded i)
  · rintro ⟨w,_,_,h⟩
    exact ⟨w,h⟩

end QuiverProofs.BoundedClassification
