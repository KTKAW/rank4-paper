import QuiverProofs.ProperEndpointVerification

/-! An unconditional rank-four acyclic endpoint theorem. The finite calculation
uses signs only. Acyclicity rules out cancellation in one mutation, and the
lifting lemmas apply to arbitrary integer weights. Total properness is used
only for the original class and its one-step descendants. -/
namespace QuiverProofs.ProperEndpoint
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
open ProperMutationRepresentativeChoice ProperObstructionSoundness
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private def FiniteEndpoint (code : Fin 729) (i : Fin 6) : Prop :=
  let B := pattern code
  (∃ t : Fin 24, Topological B (permutation t)) → ProperClassTable B i →
    (∃ t : Fin 24, Topological B (permutation t) ∧
      component (supportMask B) i = component (supportMask B) (canonicalIndex t)) ∨
    (∃ k : Fin 4, ∃ j : Fin 6, ∃ c : Fin 4,
      component (supportMask B) i = component (supportMask B) (canonicalIndex (firstIndex k j)) ∧
      Cut B (firstOrder k j) c ∧
      ¬ProperClassTable (mutate B k) (resultIndex k j c))

private instance (code : Fin 729) (i : Fin 6) : Decidable (FiniteEndpoint code i) := by
  unfold FiniteEndpoint
  infer_instance

/-- Exhausts all 729 orientations with absent edges and all six cyclic orders.
An acyclic proper class either contains a topological order or has an explicit
one-step proper mutation to a class which is not proper. -/
private theorem finite_endpoint : ∀ code : Fin 729, ∀ i : Fin 6,
    FiniteEndpoint code i := by
  intro code i htop hproper
  have h := ProperEndpointData.certificate_valid code i
  cases hw : ProperEndpointData.certificate code i with
  | cyclic =>
    rw [hw] at h
    exact False.elim (h htop)
  | improper =>
    rw [hw] at h
    exact False.elim (h hproper)
  | topological t =>
    rw [hw] at h
    exact Or.inl ⟨t,h⟩
  | bad k j c =>
    rw [hw] at h
    exact Or.inr ⟨k,j,c,h⟩

private theorem signProxy_pos (x : Int) : 0 < signProxy x ↔ 0 < x := by
  unfold signProxy
  split <;> (try split) <;> omega

private theorem proxy_properVertex (B : Matrix 4) (p : CyclicOrder) (v : Fin 4) :
    ProperVertex (proxyMatrix B) p v ↔ ProperVertex B p v := by
  unfold ProperVertex proxyMatrix
  simp only [signProxy_pos]

theorem proxy_wiggle_iff (B : Matrix 4) (p q : CyclicOrder) :
    WiggleEquivalent (proxyMatrix B) p q ↔ WiggleEquivalent B p q :=
  ⟨wiggle_zero_transfer _ _ (fun i j => (signProxy_zero (B i j)).mp),wiggle_proxy B⟩

theorem proxy_properClass (B : Matrix 4) (p : CyclicOrder) :
    ProperClass (proxyMatrix B) p ↔ ProperClass B p := by
  unfold ProperClass
  simp only [proxy_wiggle_iff,proxy_properVertex]

private theorem proxy_topological (B : Matrix 4) (p : CyclicOrder) :
    Topological (proxyMatrix B) p ↔ Topological B p := by
  unfold Topological proxyMatrix
  simp only [signProxy_nonneg]

private theorem signProxy_idem (x : Int) : signProxy (signProxy x) = signProxy x := by
  unfold signProxy
  repeat' split <;> omega

private theorem signProxy_congr_mutation (x y z : Int)
    (hp : 0 < x → 0 < y → 0 ≤ z) (hn : x < 0 → y < 0 → z ≤ 0) :
    signProxy (z + correction x y) =
      signProxy (signProxy z + correction (signProxy x) (signProxy y)) := by
  by_cases hx0 : x=0
  · simp [hx0,signProxy,correction]
    exact (signProxy_idem z).symm
  by_cases hy0 : y=0
  · simp [hy0,signProxy,correction]
    exact (signProxy_idem z).symm
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · have hprod := Int.mul_pos (show 0 < -x by omega) (show 0 < -y by omega)
      have hz := hn hx hy
      have hc : correction x y = -((-x)*(-y)) := by
        simp [correction,Int.max_def,show x ≤ 0 by omega,show y ≤ 0 by omega,
          show ¬ -x ≤ 0 by omega,show ¬ -y ≤ 0 by omega]
      rw [hc]
      have hout : z + -((-x)*(-y)) < 0 := by omega
      simp only [signProxy,hout,hx,hy,if_true]
      by_cases hz0 : z=0 <;> simp [hz0,show z < 0 ↔ z ≠ 0 by omega,correction,Int.max_def]
    · have hc : correction x y=0 := by
        simp [correction,Int.max_def,show x ≤ 0 by omega,show ¬y ≤ 0 by omega,
          show ¬ -x ≤ 0 by omega,show -y ≤ 0 by omega]
      rw [hc]
      simpa [signProxy,hx,hy,hy0,correction,Int.max_def] using (signProxy_idem z).symm
  · by_cases hy : y < 0
    · have hc : correction x y=0 := by
        simp [correction,Int.max_def,show ¬x ≤ 0 by omega,show y ≤ 0 by omega,
          show -x ≤ 0 by omega,show ¬ -y ≤ 0 by omega]
      rw [hc]
      simpa [signProxy,hx,hx0,hy,correction,Int.max_def] using (signProxy_idem z).symm
    · have hxp : 0 < x := by omega
      have hyp : 0 < y := by omega
      have hprod := Int.mul_pos hxp hyp
      have hz := hp hxp hyp
      have hc : correction x y = x*y := by
        simp [correction,Int.max_def,show ¬x ≤ 0 by omega,show ¬y ≤ 0 by omega,
          show -x ≤ 0 by omega,show -y ≤ 0 by omega]
      rw [hc]
      have hout : ¬z+x*y < 0 := by omega
      have hout0 : z+x*y ≠ 0 := by omega
      simp only [signProxy,hout,hout0,hx,hx0,hy,hy0,if_false]
      by_cases hz0 : z=0 <;> simp [hz0,show ¬z < 0 by omega,correction,Int.max_def]

/-- Absence of directed triangles prevents arrow cancellation in a single
mutation. This local hypothesis includes chordless oriented four-cycles. -/
theorem proxy_mutation_of_no_directed_triangle (B : Matrix 4) (hB : SkewSymmetric B)
    (htri : ∀ i j k, 0 < B i k → 0 < B k j → 0 ≤ B i j) (k : Fin 4) :
    proxyMatrix (mutate B k) = proxyMatrix (mutate (proxyMatrix B) k) := by
  funext i j
  by_cases hk : i=k ∨ j=k
  · simp only [proxyMatrix,mutate,hk,if_true,signProxy_neg,signProxy_idem]
  · simp only [proxyMatrix,mutate,hk,if_false]
    apply signProxy_congr_mutation
    · exact htri i j k
    · intro hik hkj
      have hki : 0 < B k i := by have := hB i k; omega
      have hjk : 0 < B j k := by have := hB k j; omega
      have h := htri j i k hjk hki
      have := hB i j
      omega

/-- In an acyclic skew matrix, mutation has no cancellation between an
existing arrow and the arrows contributed by a two-step path. Therefore the
signs after one mutation are determined by the original signs alone. -/
theorem acyclic_proxy_mutation (B : Matrix 4) (hB : SkewSymmetric B)
    (hA : Acyclic B) (k : Fin 4) :
    proxyMatrix (mutate B k) = proxyMatrix (mutate (proxyMatrix B) k) := by
  apply proxy_mutation_of_no_directed_triangle B hB
  obtain ⟨rank,hr⟩ := hA
  intro i j k hik hkj
  have hi := hr i k hik
  have hj := hr k j hkj
  by_cases hz : 0 ≤ B i j
  · exact hz
  have hji : 0 < B j i := by have := hB i j; omega
  have := hr j i hji
  omega

/-- Acyclic one-step properness already identifies the topological wiggle
class in rank four. This is stronger than the endpoint bridge, since it uses
neither uniqueness for arbitrary quivers nor unbounded total properness. -/
theorem acyclic_oneStep_endpoint (B : Matrix 4) (hB : SkewSymmetric B)
    (hA : Acyclic B) (p : CyclicOrder) (hp : ProperClass B p)
    (hstep : ∀ k q, ProperMutation B p k q → ProperClass (mutate B k) q) :
    ∃ q : CyclicOrder, Topological B q ∧ WiggleEquivalent B p q := by
  obtain ⟨code,hcode⟩ := proxy_pattern B hB
  have hs : SkewSymmetric (pattern code) := ofSix_skew _ _ _ _ _ _
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have hclass : ProperClass (pattern code) p := by
    rw [←hcode]
    exact (proxy_properClass B p).mpr hp
  have htable := (properClass_iff_table _ hs p i hi).mp hclass
  have htop : ∃ t : Fin 24, Topological (pattern code) (permutation t) := by
    obtain ⟨q,hq⟩ := AcyclicTargets.acyclic_has_topological_coordinates B hB hA
    obtain ⟨t,ht⟩ := permutation_exhaustive q
    refine ⟨t,?_⟩
    rw [←hcode]
    apply (proxy_topological B _).mpr
    simpa only [Topological,←ht] using hq
  rcases finite_endpoint code i htop htable with ⟨t,ht,hcomp⟩ | ⟨k,j,c,hcomp,hcut,hbad⟩
  · refine ⟨permutation t,?_,?_⟩
    · rw [←hcode] at ht
      exact (proxy_topological B _).mp ht
    · have hw := (wiggle_iff_component _ hs p (permutation t) i (canonicalIndex t)
        hi (canonical_index_correct t)).mpr hcomp
      rw [←hcode] at hw
      exact (proxy_wiggle_iff B _ _).mp hw
  · have hw := (wiggle_iff_component _ hs p (firstOrder k j) i
        (canonicalIndex (firstIndex k j)) hi (canonical_index_correct (firstIndex k j))).mpr hcomp
    rw [←hcode] at hw hcut
    have hfirst : (firstOrder k j).toFun 0=k := by
      exact (show ∀ (k : Fin 4) (j : Fin 6), (firstOrder k j).toFun 0=k by decide) k j
    have hm : ProperMutation B p k ((firstOrder k j).trans (cutOrder c)) :=
      ⟨firstOrder k j,c,(proxy_wiggle_iff B _ _).mp hw,hfirst,
        (cut_proxy B _ _).mp hcut,.same (fun _ _ _ => Iff.rfl)⟩
    have hout := (proxy_properClass (mutate B k) _).mpr (hstep k _ hm)
    rw [acyclic_proxy_mutation B hB hA k,hcode] at hout
    have hout' := (proxy_properClass (mutate (pattern code) k) _).mp hout
    exact False.elim (hbad ((properClass_iff_table _ (mutation_preserves_skew _ k hs) _
      (resultIndex k j c) (result_correct k j c)).mp hout'))

/-- Unconditional inhabitant of the exact endpoint proposition used by all
scalar and companion obstruction parents. -/
theorem endpointTopological4 : EndpointTopological4 := by
  intro B hB hA p hp
  exact acyclic_oneStep_endpoint B hB hA p (totalProper_proper B p hp)
    (fun k q hm => hp _ q (.step .refl hm))

end QuiverProofs.ProperEndpoint
