import QuiverProofs.ProperMutationChoiceVerification
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
/-- Every admissible representative and nonneighbor cut leads to the same
mutated wiggle class, for arbitrary skew integer rank-four matrices. -/
theorem cut_representatives_independent (B : Matrix 4) (hB : SkewSymmetric B)
    (r s : CyclicOrder) (k : Fin 4) (c d : Fin 4)
    (hr : r.toFun 0=k) (hs : s.toFun 0=k)
    (hw : WiggleEquivalent B r s) (hc : Cut B r c) (hd : Cut B s d) :
    WiggleEquivalent (mutate B k) (r.trans (cutOrder c)) (s.trans (cutOrder d)) := by
  obtain ⟨i,rfl⟩ := first_order_exhaustive r k hr
  obtain ⟨j,rfl⟩ := first_order_exhaustive s k hs
  obtain ⟨code,hp⟩ := proxy_pattern B hB
  have hsource := wiggle_component (proxyMatrix B) (proxy_skew B hB) (wiggle_proxy B hw)
    (canonicalIndex (firstIndex k i)) (canonicalIndex (firstIndex k j))
    (canonical_index_correct (firstIndex k i)) (canonical_index_correct (firstIndex k j))
  have hcuti := (cut_proxy B (firstOrder k i) c).mpr hc
  have hcutj := (cut_proxy B (firstOrder k j) d).mpr hd
  rw [hp] at hsource hcuti hcutj
  have htarget := finite_choice_independence code k i j c d hcuti hcutj hsource
  rw [←hp] at htarget
  have hwiggle := (wiggle_iff_component (mutate (proxyMatrix B) k)
    (mutation_preserves_skew _ k (proxy_skew B hB))
    ((firstOrder k i).trans (cutOrder c)) ((firstOrder k j).trans (cutOrder d))
    (resultIndex k i c) (resultIndex k j d) (result_correct k i c) (result_correct k j d)).mpr htarget
  exact wiggle_zero_transfer _ _ (proxy_mutation_zero B k) hwiggle

/-- Proper mutation is well defined on wiggle classes, including independence
of both the initial representative and the chosen nonneighbor cut. -/
theorem properMutation_class_independent (B : Matrix 4) (hB : SkewSymmetric B)
    {p p' q q' : CyclicOrder} {k : Fin 4}
    (hpp' : WiggleEquivalent B p p')
    (h : ProperMutation B p k q) (h' : ProperMutation B p' k q') :
    WiggleEquivalent (mutate B k) q q' := by
  obtain ⟨r,c,hpr,hr,hc,hrq⟩ := h
  obtain ⟨s,d,hps,hs,hd,hsq⟩ := h'
  have hrs := WiggleEquivalent.trans (wiggle_symmetric B hB hpr)
    (WiggleEquivalent.trans hpp' hps)
  have hcut := cut_representatives_independent B hB r s k c d hr hs hrs hc hd
  exact .trans (wiggle_symmetric _ (mutation_preserves_skew B k hB) hrq) (.trans hcut hsq)

theorem properMutation_target_unique (B : Matrix 4) (hB : SkewSymmetric B)
    {p q q' : CyclicOrder} {k : Fin 4}
    (h : ProperMutation B p k q) (h' : ProperMutation B p k q') :
    WiggleEquivalent (mutate B k) q q' :=
  properMutation_class_independent B hB (.same (fun _ _ _ => Iff.rfl)) h h'

end QuiverProofs.ProperMutationRepresentativeChoice
