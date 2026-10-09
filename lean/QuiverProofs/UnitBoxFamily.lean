import QuiverProofs.DependentProperConsequences
import QuiverProofs.MissingEdgeRays
import QuiverProofs.Pendant

/-! The boundary family with one unit alternating weight. The symbolic
mutation ray and its language obstruction are unconditional. The scalar NMA
deduction explicitly retains the two currently missing structural bridges;
global triangle avoidance is not asserted. -/
namespace QuiverProofs.UnitBoxFamily
open ProperOrder ProperWiggle ProperObstructionSoundness Census
open MissingEdgeRays
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def quiver (b : Int) : Matrix 4 := ofSix (-1) 0 b (-b) 0 (-1)
def first (b : Int) : Matrix 4 := ofSix 1 0 (-b) (-b) b (-1)
def ray (d : Int) (s : State) : Matrix 4 := ofSix (-1) 0 0 s.x (-s.y) d

theorem first_mutation (b : Int) (hb : 1≤b) : mutate (quiver b) 0 = first b := by
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [quiver,first,mutate,ofSix,correction] <;> grind

theorem entry_word (b : Int) (hb : 1≤b) :
    applyWord (quiver b) [0,1] = ray (b*b-1) ⟨b,b⟩ := by
  simp only [applyWord]
  rw [first_mutation b hb]
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [first,ray,mutate,ofSix,correction] <;> grind

/-- The excluded parameter b=1 has the exact two-mutation acyclic witness. -/
theorem boundary_one_acyclic : Acyclic (applyWord (quiver 1) [0,1]) := by
  rw [entry_word 1 (by decide)]
  refine ⟨fun i => if i=3 then 0 else if i=1 then 1 else 2,?_⟩
  intro i j hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [ray,ofSix]

theorem boundary_one_MA : MutationAcyclic (quiver 1) := ⟨[0,1],boundary_one_acyclic⟩

/-- New-to-old labels put the reached pendant vertex in the standard ray. -/
def rayOrder : Relabeling 4 := Census.permutation 3

theorem ray_relabel (d : Int) (s : State) :
    relabel (ray d s) rayOrder = MissingEdgeRays.Pendant.quiver (-1) d s := by
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    first | rfl | exact Int.neg_neg _ | exact (Int.neg_neg _).symm

/-- Chronological words in the manuscript's original labels. -/
def word (n : Nat) : List (Fin 4) :=
  [0,1] ++ (MissingEdgeRays.Pendant.word n).map rayOrder.toFun

def state (b : Int) (n : Nat) : State := MissingEdgeRays.Pendant.orbit (b*b-1) ⟨b,b⟩ n

private theorem parameter_bound (b : Int) (hb : 2≤b) : 3≤b*b-1 := by
  have h := Int.mul_le_mul_of_nonneg_left hb (show 0≤b by omega)
  omega

/-- Every repeated (3,2) block implements the two-dimensional recurrence. -/
theorem ray_as_mutations (b : Int) (hb : 2≤b) (n : Nat) :
    applyWord (quiver b) (word n) = ray (b*b-1) (state b n) := by
  have he : relabel (applyWord (quiver b) (word n)) rayOrder =
      relabel (ray (b*b-1) (state b n)) rayOrder := by
    rw [word,applyWord_append,entry_word b (by omega),←word_relabel,ray_relabel,
      MissingEdgeRays.Pendant.orbit_as_mutations (-1) (b*b-1) ⟨b,b⟩
        (parameter_bound b hb) (by unfold MissingEdgeRays.Pendant.domain; simp; omega) n,
      ray_relabel]
    rfl
  have := congrArg (fun Q : Matrix 4 => relabel Q rayOrder.symm) he
  simpa only [relabel_inverse] using this

theorem state_domain (b : Int) (hb : 2≤b) (n : Nat) :
    0 < (state b n).x ∧ (state b n).x ≤ (state b n).y :=
  MissingEdgeRays.Pendant.orbit_domain (b*b-1) ⟨b,b⟩ (parameter_bound b hb)
    (by unfold MissingEdgeRays.Pendant.domain; simp; omega) n

theorem state_growth (b : Int) (hb : 2≤b) (n : Nat) :
    5*(state b n).y ≤ (state b (n+1)).y :=
  (MissingEdgeRays.Pendant.step_domain_and_growth (b*b-1) (state b n)
    (parameter_bound b hb) (state_domain b hb n)).2

theorem persistent_missing_pairs (b : Int) (hb : 2≤b) (n : Nat) :
    applyWord (quiver b) (word n) 0 2 = 0 ∧
    applyWord (quiver b) (word n) 0 3 = 0 := by
  rw [ray_as_mutations b hb n]
  exact ⟨rfl,rfl⟩

theorem ray_two_weak_pairs (d : Int) (s : State) :
    ExtendedWeakPairs.TwoWeakPairs (ray d s) :=
  ⟨0,2,0,3,by simp [ExtendedWeakPairs.Weak,ray,ofSix],
    by simp [ExtendedWeakPairs.Weak,ray,ofSix],by simp [ExtendedWeakPairs.SamePair]⟩

theorem ray_nonfork (b : Int) (hb : 2≤b) (n : Nat) (r : Fin 4) :
    ¬ ForkDefinition.GraphFork (applyWord (quiver b) (word n)) r := by
  intro hf
  have hab := hf.2.2.1 0 2 (by decide)
  rw [(persistent_missing_pairs b hb n).1] at hab
  contradiction

theorem escapes_finite_core_and_exterior (b : Int) (hb : 2≤b)
    (candidates : List (Matrix 4)) :
    ∃ n, (∀ B∈candidates, ∀ p : Relabeling 4,
      applyWord (quiver b) (word n) ≠ relabel B p) ∧
      ¬ ExtendedWeakPairs.Exterior (applyWord (quiver b) (word n)) := by
  obtain ⟨n,hn⟩ := escapes_of_unbounded_entry (fun n => applyWord (quiver b) (word n)) 3 1
    (by
      intro bound
      obtain ⟨n,hn⟩ := MissingEdgeRays.Pendant.orbit_y_unbounded (b*b-1) ⟨b,b⟩
        (parameter_bound b hb) (by unfold MissingEdgeRays.Pendant.domain; simp; omega) bound
      exact ⟨n,by dsimp only; rw [ray_as_mutations b hb n]; simpa [ray,ofSix,state] using hn⟩) candidates
  refine ⟨n,fun B hB p => hn B hB p.toFun,?_⟩
  rw [ray_as_mutations b hb n]
  exact ExtendedWeakPairs.two_not_exterior (ray_two_weak_pairs _ _)

theorem no_finite_core_exterior_cover (b : Int) (hb : 2≤b) :
    ¬ ExtendedWeakPairs.FiniteCoreExteriorCover (quiver b) := by
  rintro ⟨candidates,hcover⟩
  obtain ⟨n,hn,hext⟩ := escapes_finite_core_and_exterior b hb candidates
  rcases hcover (word n) with ⟨B,hB,p,hp⟩ | h
  · exact hn B hB p hp
  · exact hext h

/-- The two missing pairs persist after either intermediate phase of every block. -/
theorem every_phase_missing_pairs (b : Int) (hb : 2≤b) (n : Nat) (phase : Fin 2) :
    applyWord (quiver b) (word n ++ ([3,2] : List (Fin 4)).take phase.val) 0 2 = 0 ∧
    applyWord (quiver b) (word n ++ ([3,2] : List (Fin 4)).take phase.val) 0 3 = 0 := by
  rw [applyWord_append,ray_as_mutations b hb n]
  have hp : phase=0 ∨ phase=1 := by omega
  rcases hp with rfl|rfl
  · exact ⟨rfl,rfl⟩
  · simp [List.take,applyWord,ray,mutate,ofSix,correction]

theorem every_phase_nonfork (b : Int) (hb : 2≤b) (n : Nat) (phase : Fin 2) (r : Fin 4) :
    ¬ ForkDefinition.GraphFork
      (applyWord (quiver b) (word n ++ ([3,2] : List (Fin 4)).take phase.val)) r := by
  intro hf
  have hab := hf.2.2.1 0 2 (by decide)
  rw [(every_phase_missing_pairs b hb n phase).1] at hab
  contradiction

private theorem fin3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by omega

/-- The complementary triangle at the pendant entry has an explicit two-step witness. -/
theorem entry_deletion_MA (b : Int) (hb : 1≤b) :
    MutationAcyclic (TriangleRegions.restrict (ray (b*b-1) ⟨b,b⟩)
      (TriangleRegions.deleteVertex 0)) := by
  have he : applyWord (TriangleRegions.restrict (ray (b*b-1) ⟨b,b⟩)
      (TriangleRegions.deleteVertex 0)) [0,1] = cycleThree b 1 0 := by
    funext i j
    rcases fin3 i with rfl|rfl|rfl <;> rcases fin3 j with rfl|rfl|rfl <;>
      simp [TriangleRegions.restrict,TriangleRegions.deleteVertex,ray,ofSix,
        applyWord,mutate,correction,cycleThree] <;> grind
  refine ⟨[0,1],?_⟩
  rw [he]
  exact cycleThree_acyclic_z_nonpos b 1 0 (by omega) (by decide) (by decide)

/-- Every word omitting the attachment vertex after entry preserves the pendant
and has only MA induced triangles. Words involving that vertex are not included. -/
theorem pendant_suborbit (b : Int) (hb : 1≤b) (w : List (Fin 4)) (hw : 1∉w) :
    QuiverProofs.Pendant.At (applyWord (quiver b) ([0,1]++w)) 0 1 ∧
    TriangleRegions.AllTrianglesMA (applyWord (quiver b) ([0,1]++w)) := by
  rw [applyWord_append,entry_word b hb]
  apply QuiverProofs.Pendant.pendant_suborbits_of_deletion _ (ofSix_skew _ _ _ _ _ _)
    0 1 _ (entry_deletion_MA b hb) w hw
  refine ⟨by decide,by simp [ofSix],?_⟩
  intro j hj
  rcases fin4 j with rfl|rfl|rfl|rfl <;> simp_all [ofSix]

private theorem first_table_iff (b : Int) (hb : 1≤b) (i : Fin 6) :
    ProperClassTable (first b) i ↔ i=1 ∨ i=2 := by
  have hm : supportMask (first b)=supportMask (first 1) := by
    simp [first,supportMask,supportBit,ofSix,show b≠0 by omega,show -b≠0 by omega]
  have hs : ∀ i j, 0<first b i j ↔ 0<first 1 i j := by
    intro i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [first,ofSix] <;> omega
  exact (ChamberProperness.properClassTable_sign_iff (first b) (first 1) hm hs i).trans
    ((show ∀ i : Fin 6, ProperClassTable (first 1) i ↔ i=1 ∨ i=2 by decide) i)

/-- Every b>=1 has precisely the displayed proper wiggle class after mutation 0. -/
theorem first_proper_class_iff (b : Int) (hb : 1≤b) (p : CyclicOrder) :
    ProperClass (first b) p ↔ WiggleEquivalent (first b) p (order 1) := by
  have hB : SkewSymmetric (first b) := ofSix_skew _ _ _ _ _ _
  have hbase : ProperClass (first b) (order 1) := by
    apply (properClass_iff_table (first b) hB (order 1) 1 (fun _ _ _ => Iff.rfl)).mpr
    exact (first_table_iff b hb 1).mpr (Or.inl rfl)
  constructor
  · intro hp
    obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
    have ht := (properClass_iff_table (first b) hB p i hi).mp hp
    have hi12 := (first_table_iff b hb i).mp ht
    apply (wiggle_iff_component (first b) hB p (order 1) i 1 hi
      (fun _ _ _ => Iff.rfl)).mpr
    have hm : supportMask (first b)=61 := by
      simp [first,supportMask,supportBit,ofSix,show b≠0 by omega,show -b≠0 by omega]
    rw [hm]
    rcases hi12 with rfl|rfl <;> decide
  · intro h
    exact (properClass_wiggle (first b) hB h).mpr hbase

theorem first_proper_markov (b : Int) (hb : 1≤b) (p : CyclicOrder)
    (hp : ProperClass (first b) p) : orderMarkov (first b) p = b*b+2 := by
  rw [ProperWiggleInvariants.markov_wiggle_invariant (first b)
    (ofSix_skew _ _ _ _ _ _) ((first_proper_class_iff b hb p).mp hp)]
  change Algebra.markov 1 (-b) 0 b (-b) 1 = _
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  grind

theorem first_pfaffian (b : Int) : matrixPfaffian (first b) = b*b-1 := by
  simp [first,matrixPfaffian,ofSix]
  grind

private theorem first_connected (b : Int) (hb : 1≤b) : ConnectedSupport (first b) := by
  apply (connected_iff_all_colorings _).mpr
  intro color hc i j
  have h01 := hc 0 1 (by simp [first,ofSix])
  have h03 := hc 0 3 (by simp [first,ofSix]; omega)
  have h12 := hc 1 2 (by simp [first,ofSix]; omega)
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;> simp_all

/-- The all-parameter arithmetic exclusion is independent of the structural
bridges: no connected topological tuple has the required proper invariants. -/
theorem scalar_exclusion (b : Int) (hb : 2≤b) (p : CyclicOrder)
    (hp : ProperClass (first b) p) (C : Matrix 4) (hC : SkewSymmetric C)
    (hconn : ConnectedSupport C) (q : CyclicOrder) (hq : Topological C q)
    (hm : orderMarkov C q = orderMarkov (first b) p)
    (hD : matrixPfaffian C^2 = matrixPfaffian (first b)^2) : False := by
  have hM := hm.trans (first_proper_markov b (by omega) p hp)
  have hconnq := connected_relabel C q hconn
  rw [←ofSix_reconstruct (relabel C q) (relabel_skew C q hC)] at hconnq
  have hcuts := DependentProperConsequences.connectedSupport_firstGap _ _ _ _ _ _ hconnq
  have hbound := FirstGap.connected_strict_pfaffian_bound _ _ _ _ _ _
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2 hcuts
  have hsquare : matrixPfaffian (relabel C q)^2 = (b*b-1)^2 := by
    rw [ClassSeparation.pfaffian_square_relabel C hC q,hD,first_pfaffian]
  have hb2 := parameter_bound b hb
  have hPabs : ((matrixPfaffian (relabel C q)).natAbs : Int) = b*b-1 := by
    rcases ClassSeparation.square_eq_cases _ _ hsquare with h|h
    · rw [h,Int.natAbs_of_nonneg (by omega)]
    · rw [h,Int.natAbs_neg,Int.natAbs_of_nonneg (by omega)]
  change 2*((matrixPfaffian (relabel C q)).natAbs : Int) < orderMarkov C q at hbound
  omega

/-- Conditional NMA reduction, deliberately separate from the unconditional
ray and scalar-exclusion results above. -/
theorem NMA_of_bridges (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b : Int) (hb : 2≤b) : ¬ MutationAcyclic (quiver b) := by
  have hn : ¬MutationAcyclic (first b) :=
    NMA_of_scalar_exclusion hExist hEnd (first b) (ofSix_skew _ _ _ _ _ _)
      (first_connected b (by omega)) (scalar_exclusion b hb)
  intro hMA
  have h := (mutationAcyclic_iff (quiver b) 0).mpr hMA
  rw [first_mutation b (by omega)] at h
  exact hn h

end QuiverProofs.UnitBoxFamily
