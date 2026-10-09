import QuiverProofs.ProperObstructionSoundness
import QuiverProofs.Chamber
import QuiverProofs.Cosquare

/-! The missing proper-transport half of the five-parameter chamber theorem.
Its failure of total properness is unconditional and unbounded. The NMA
conclusion has exactly the explicit MA-to-total-properness hypothesis. -/
namespace QuiverProofs.ChamberProperness
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness Census
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

/-- Vertex properness depends only on the directed support, not its weights. -/
theorem properVertex_sign_iff (A B : Matrix 4)
    (h : ∀ i j, 0 < A i j ↔ 0 < B i j) (p : CyclicOrder) (v : Fin 4) :
    ProperVertex A p v ↔ ProperVertex B p v := by
  constructor
  · intro hp u w huv hvw
    exact hp u w ((h u v).mpr huv) ((h v w).mpr hvw)
  · intro hp u w huv hvw
    exact hp u w ((h u v).mp huv) ((h v w).mp hvw)

theorem properClassTable_sign_iff (A B : Matrix 4)
    (hm : supportMask A=supportMask B)
    (h : ∀ i j, 0 < A i j ↔ 0 < B i j) (i : Fin 6) :
    ProperClassTable A i ↔ ProperClassTable B i := by
  constructor
  · intro hp v
    obtain ⟨j,hj,hv⟩ := hp v
    exact ⟨j,by simpa only [hm] using hj,(properVertex_sign_iff A B h _ v).mp hv⟩
  · intro hp v
    obtain ⟨j,hj,hv⟩ := hp v
    exact ⟨j,by simpa only [hm] using hj,(properVertex_sign_iff A B h _ v).mpr hv⟩

private def initialSeed : Matrix 4 := ofSix 0 (-1) 1 (-1) (-1) (-1)
private def targetSeed : Matrix 4 := ofSix 0 1 (-1) (-1) (-1) 1

private theorem support_initial (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v) :
    supportMask (ofSix 0 (-x) y (-z) (-u) (-v))=62 := by
  have hx0 : -x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hz0 : -z ≠ 0 := by omega
  have hu0 : -u ≠ 0 := by omega
  have hv0 : -v ≠ 0 := by omega
  simp [supportMask,supportBit,ofSix,hx0,hy0,hz0,hu0,hv0]

private theorem initial_signs (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v) :
    ∀ i j, 0 < ofSix 0 (-x) y (-z) (-u) (-v) i j ↔ 0 < initialSeed i j := by
  intro i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [ofSix,initialSeed] <;> omega

/-- For every positive magnitude, the only initial proper wiggle class is
represented by (0,1,3,2), also represented by (0,3,2,1). -/
theorem initial_proper_class (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v)
    (p : CyclicOrder) (hp : ProperClass (ofSix 0 (-x) y (-z) (-u) (-v)) p) :
    WiggleEquivalent (ofSix 0 (-x) y (-z) (-u) (-v)) p (order 1) := by
  let Q := ofSix 0 (-x) y (-z) (-u) (-v)
  have hQ : SkewSymmetric Q := ofSix_skew _ _ _ _ _ _
  have hm : supportMask Q=62 := support_initial x y z u v hx hy hz hu hv
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q hQ p i hi).mp hp
  have hs : supportMask Q=supportMask initialSeed := by
    rw [hm]; exact (show supportMask initialSeed=62 by decide).symm
  have hseed := (properClassTable_sign_iff Q initialSeed hs
    (initial_signs x y z u v hx hy hz hu hv) i).mp ht
  have he : i=1 ∨ i=5 := (show ∀ i : Fin 6,
    ProperClassTable initialSeed i → i=1 ∨ i=5 by decide) i hseed
  apply (wiggle_iff_component Q hQ p (order 1) i 1 hi (fun _ _ _ => Iff.rfl)).mpr
  rw [hm]
  rcases he with rfl|rfl <;> decide

private theorem target_not_proper (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hfail : v<x*y) :
    ¬ ProperClass (ofSix 0 x (-y) (-z) (-u) (x*y-v)) (order 2) := by
  let Q := ofSix 0 x (-y) (-z) (-u) (x*y-v)
  have hQ : SkewSymmetric Q := ofSix_skew _ _ _ _ _ _
  have hmask : supportMask Q=supportMask targetSeed := by
    have hx0 : x ≠ 0 := by omega
    have hy0 : -y ≠ 0 := by omega
    have hz0 : -z ≠ 0 := by omega
    have hu0 : -u ≠ 0 := by omega
    have hv0 : x*y-v ≠ 0 := by omega
    simp [Q,targetSeed,supportMask,supportBit,ofSix,hx0,hy0,hz0,hu0,hv0]
  have hsign : ∀ i j, 0 < Q i j ↔ 0 < targetSeed i j := by
    intro i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [Q,targetSeed,ofSix] <;> omega
  intro hp
  have ht := (properClass_iff_table Q hQ (order 2) 2 (fun _ _ _ => Iff.rfl)).mp hp
  have hs := (properClassTable_sign_iff Q targetSeed hmask hsign 2).mp ht
  exact (show ¬ ProperClassTable targetSeed 2 by decide) hs

/-- The advertised initial proper class exists for every positive magnitude,
so the class description is sound as well as exclusive. -/
theorem initial_class_proper (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v) :
    ProperClass (ofSix 0 (-x) y (-z) (-u) (-v)) (order 1) := by
  let Q := ofSix 0 (-x) y (-z) (-u) (-v)
  have hQ : SkewSymmetric Q := ofSix_skew _ _ _ _ _ _
  have hs : supportMask Q=supportMask initialSeed := by
    rw [support_initial x y z u v hx hy hz hu hv]
    exact (show supportMask initialSeed=62 by decide).symm
  apply (properClass_iff_table Q hQ (order 1) 1 (fun _ _ _ => Iff.rfl)).mpr
  apply (properClassTable_sign_iff Q initialSeed hs
    (initial_signs x y z u v hx hy hz hu hv) 1).mpr
  exact (show ProperClassTable initialSeed 1 by decide)

/-- The proper mutation used in the manuscript, with its actual transported
class. Nonneighbors are allowed on either side of the cut. -/
theorem initial_proper_mutation (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v)
    (p : CyclicOrder) (hp : ProperClass (ofSix 0 (-x) y (-z) (-u) (-v)) p) :
    ProperMutation (ofSix 0 (-x) y (-z) (-u) (-v)) p 0 (order 2) := by
  refine ⟨order 1,2,initial_proper_class x y z u v hx hy hz hu hv p hp,rfl,?_,?_⟩
  · change 0 ≤ 0 ∧ 0 ≤ y ∧ -x ≤ 0
    omega
  · exact .same (by decide)

/-- No cyclic ordering of this positive chamber is totally proper when
xy>v. The conclusion quantifies over all proper descendants by definition. -/
theorem five_parameter_not_totalProper (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v) (hfail : v<x*y)
    (p : CyclicOrder) : ¬ TotalProper (ofSix 0 (-x) y (-z) (-u) (-v)) p := by
  intro htp
  have hp := totalProper_proper _ p htp
  have hm := initial_proper_mutation x y z u v hx hy hz hu hv p hp
  have ht : Transport (ofSix 0 (-x) y (-z) (-u) (-v)) p
      (mutate (ofSix 0 (-x) y (-z) (-u) (-v)) 0) (order 2) := .step .refl hm
  have htarget := htp _ _ ht
  rw [five_parameter_mutation x y z u v hx hy] at htarget
  exact target_not_proper x y z u v hx hy hz hu hfail htarget

/-- The NMA converse depends only on the stated external existence bridge.
It does not need endpoint identification, companion invariance or uniqueness. -/
theorem five_parameter_NMA (hExist : MAHasTotalProper4) (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v) (hfail : v<x*y) :
    ¬ MutationAcyclic (ofSix 0 (-x) y (-z) (-u) (-v)) := by
  intro hMA
  obtain ⟨p,hp⟩ := hExist _ (ofSix_skew _ _ _ _ _ _) hMA
  exact five_parameter_not_totalProper x y z u v hx hy hz hu hv hfail p hp

/-- Exact five-parameter decision, explicitly conditional on Neville's
MA-to-total-properness bridge in the current semantics. Equality is included. -/
theorem five_parameter_MA_iff (hExist : MAHasTotalProper4) (x y z u v : Int)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hu : 0<u) (hv : 0<v) :
    MutationAcyclic (ofSix 0 (-x) y (-z) (-u) (-v)) ↔ x*y≤v := by
  constructor
  · intro hMA
    by_cases h : x*y≤v
    · exact h
    · exact False.elim (five_parameter_NMA hExist x y z u v hx hy hz hu hv (by omega) hMA)
  · exact five_parameter_MA x y z u v hx hy hz hu

/-- The displayed cosquare-collision seed already loses properness after one
proper mutation in its sole initial proper class. This is an actual depth-one
witness, independent of its separate cosquare similarity. -/
theorem delayed_Q_depth_one_failure :
    ProperClass Cosquare.delayedQ (order 1) ∧
    ProperMutation Cosquare.delayedQ (order 1) 0 (order 2) ∧
    ¬ ProperClass (mutate Cosquare.delayedQ 0) (order 2) := by
  have hp := initial_class_proper 1 3 2 2 2 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨hp,initial_proper_mutation 1 3 2 2 2 (by decide) (by decide)
    (by decide) (by decide) (by decide) (order 1) hp,?_⟩
  rw [show Cosquare.delayedQ=ofSix 0 (-1) 3 (-2) (-2) (-2) from rfl,
    five_parameter_mutation 1 3 2 2 2 (by decide) (by decide)]
  exact target_not_proper 1 3 2 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem delayed_Q_not_totalProper (p : CyclicOrder) :
    ¬ TotalProper Cosquare.delayedQ p :=
  five_parameter_not_totalProper 1 3 2 2 2 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) p

theorem delayed_Q_NMA (hExist : MAHasTotalProper4) :
    ¬ MutationAcyclic Cosquare.delayedQ :=
  five_parameter_NMA hExist 1 3 2 2 2 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end QuiverProofs.ChamberProperness
