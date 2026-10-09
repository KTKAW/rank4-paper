import QuiverProofs.ProperMutationRepresentativeChoice

/-! Saturation and total-properness semantics on complete wiggle classes.
Representative independence is supplied by the shared, kernel-checked
ProperMutationRepresentativeChoice module. -/
namespace QuiverProofs.ProperMutationIndependence
open ProperOrder ProperWiggle ProperMutation

/-- Choosing a different input representative changes neither availability
nor possible output classes of proper mutation. -/
theorem properMutation_input_wiggle (B : Matrix 4) (hB : SkewSymmetric B)
    {p q r : CyclicOrder} {k : Fin 4} (hw : WiggleEquivalent B p q) :
    ProperMutation B p k r ↔ ProperMutation B q k r := by
  constructor
  · rintro ⟨s,c,hps,hk,hc,hsr⟩
    exact ⟨s,c,.trans (wiggle_symmetric B hB hw) hps,hk,hc,hsr⟩
  · rintro ⟨s,c,hqs,hk,hc,hsr⟩
    exact ⟨s,c,.trans hw hqs,hk,hc,hsr⟩

/-- The proper-mutation relation is saturated on its output wiggle class. -/
theorem properMutation_output_wiggle (B : Matrix 4) (hB : SkewSymmetric B)
    {p q r : CyclicOrder} {k : Fin 4}
    (hw : WiggleEquivalent (mutate B k) q r) :
    ProperMutation B p k q ↔ ProperMutation B p k r := by
  constructor
  · rintro ⟨s,c,hps,hk,hc,hsq⟩
    exact ⟨s,c,hps,hk,hc,.trans hsq hw⟩
  · rintro ⟨s,c,hps,hk,hc,hsr⟩
    exact ⟨s,c,hps,hk,hc,.trans hsr
      (wiggle_symmetric (mutate B k) (mutation_preserves_skew B k hB) hw)⟩

/-- Finite transport started in a different representative has the same
endpoint class, including the length-zero case. -/
theorem transport_input_wiggle (B : Matrix 4) (hB : SkewSymmetric B)
    {p q : CyclicOrder} (hw : WiggleEquivalent B p q)
    {C : Matrix 4} {r : CyclicOrder} (h : Transport B q C r) :
    ∃ s : CyclicOrder, Transport B p C s ∧ WiggleEquivalent C s r := by
  induction h with
  | refl => exact ⟨p,.refl,hw⟩
  | @step C r t k ht hm ih =>
    obtain ⟨s,hs,hsr⟩ := ih
    have hC := transport_skew hB ht
    have hm' := (properMutation_input_wiggle C hC hsr).mpr hm
    exact ⟨t,.step hs hm',.same (fun _ _ _ => Iff.rfl)⟩

/-- Total properness is a property of an entire wiggle class. -/
theorem totalProper_wiggle_iff (B : Matrix 4) (hB : SkewSymmetric B)
    {p q : CyclicOrder} (hw : WiggleEquivalent B p q) :
    TotalProper B p ↔ TotalProper B q := by
  have fwd : ∀ p q, WiggleEquivalent B p q → TotalProper B p → TotalProper B q := by
    intro p q hw hp C r ht
    obtain ⟨s,hs,hsr⟩ := transport_input_wiggle B hB hw ht
    exact (properClass_wiggle C (transport_skew hB ht) hsr).mp (hp C s hs)
  exact ⟨fwd p q hw,fwd q p (wiggle_symmetric B hB hw)⟩

end QuiverProofs.ProperMutationIndependence
