import QuiverProofs.ProperObstructionSoundness

/-! Exhaustive scalar target exclusions actually used by the 83 source
certificates. The coordinate bound is proved before finite enumeration. -/
namespace QuiverProofs.ProperScalarTargets
open ProperOrder ProperWiggle ProperObstructionSoundness Census
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def ExcludedPair (m D : Int) : Prop :=
  (m=16 ∧ D=36) ∨ (m=17 ∧ D=64) ∨ (m=11 ∧ D=25) ∨
  (m=14 ∧ D=49) ∨ (m=17 ∧ D=25) ∨ (m=12 ∧ D=36) ∨
  (m=11 ∧ D=16) ∨ (m=7 ∧ D=9) ∨ (m=8 ∧ D=16) ∨
  (m=9 ∧ D=25) ∨ (m=2 ∧ D=1) ∨ (m=4 ∧ D=4) ∨ (m=6 ∧ D=9)
instance (m D : Int) : Decidable (ExcludedPair m D) := by
  unfold ExcludedPair; infer_instance

def SmallExcluded (m D : Int) : Prop :=
  ∀ a b c d e f : Fin 5,
    ¬ (Algebra.markov a.val b.val c.val d.val e.val f.val = m ∧
      Algebra.pfaffian a.val b.val c.val d.val e.val f.val ^ 2 = D ∧
      ConnectedSupport (ofSix a.val b.val c.val d.val e.val f.val))
instance (m D : Int) : Decidable (SmallExcluded m D) := by
  unfold SmallExcluded; infer_instance

private theorem small_0 : SmallExcluded 16 36 := by decide
private theorem small_1 : SmallExcluded 17 64 := by decide
private theorem small_2 : SmallExcluded 11 25 := by decide
private theorem small_3 : SmallExcluded 14 49 := by decide
private theorem small_4 : SmallExcluded 17 25 := by decide
private theorem small_5 : SmallExcluded 12 36 := by decide
private theorem small_6 : SmallExcluded 11 16 := by decide
private theorem small_7 : SmallExcluded 7 9 := by decide
private theorem small_8 : SmallExcluded 8 16 := by decide
private theorem small_9 : SmallExcluded 9 25 := by decide
private theorem small_10 : SmallExcluded 2 1 := by decide
private theorem small_11 : SmallExcluded 4 4 := by decide
private theorem small_12 : SmallExcluded 6 9 := by decide

theorem excluded_pair_small (m D : Int) (h : ExcludedPair m D) :
    SmallExcluded m D := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals first | exact small_0 | exact small_1 | exact small_2 | exact small_3 |
    exact small_4 | exact small_5 | exact small_6 | exact small_7 | exact small_8 |
    exact small_9 | exact small_10 | exact small_11 | exact small_12

private theorem coordinate_bound (x : Int) (hx : 0 ≤ x) (h : x^2 ≤ 17) : x ≤ 4 := by
  by_cases h5 : 5 ≤ x
  · have := Algebra.square_monotone 5 x (by decide) h5
    omega
  · omega

/-- Exact exhaustive enumeration: every connected nonnegative tuple is
excluded, even when its entries have no prescribed initial bound. -/
theorem excluded_pair_no_topological (m D a b c d e f : Int)
    (hpair : ExcludedPair m D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : ConnectedSupport (ofSix a b c d e f))
    (hm : Algebra.markov a b c d e f = m)
    (hD : Algebra.pfaffian a b c d e f ^ 2 = D) : False := by
  have hm17 : m ≤ 17 := by unfold ExcludedPair at hpair; omega
  obtain ⟨ha2,hb2,hc2,hd2,he2,hf2⟩ :=
    Algebra.coordinate_squares_le_markov a b c d e f ha hb hc hd he hf
  have ha4 := coordinate_bound a ha (by omega)
  have hb4 := coordinate_bound b hb (by omega)
  have hc4 := coordinate_bound c hc (by omega)
  have hd4 := coordinate_bound d hd (by omega)
  have he4 := coordinate_bound e he (by omega)
  have hf4 := coordinate_bound f hf (by omega)
  let aa : Fin 5 := ⟨a.toNat,by omega⟩
  let bb : Fin 5 := ⟨b.toNat,by omega⟩
  let cc : Fin 5 := ⟨c.toNat,by omega⟩
  let dd : Fin 5 := ⟨d.toNat,by omega⟩
  let ee : Fin 5 := ⟨e.toNat,by omega⟩
  let ff : Fin 5 := ⟨f.toNat,by omega⟩
  have ea : (aa.val : Int)=a := by dsimp [aa]; omega
  have eb : (bb.val : Int)=b := by dsimp [bb]; omega
  have ec : (cc.val : Int)=c := by dsimp [cc]; omega
  have ed : (dd.val : Int)=d := by dsimp [dd]; omega
  have eeq : (ee.val : Int)=e := by dsimp [ee]; omega
  have ef : (ff.val : Int)=f := by dsimp [ff]; omega
  apply excluded_pair_small m D hpair aa bb cc dd ee ff
  simpa only [ea,eb,ec,ed,eeq,ef] using And.intro hm (And.intro hD hconn)

/-- Canonical proper-class tables suffice to check every arbitrary order. -/
theorem scalar_exclusion_of_table (B : Matrix 4) (hB : SkewSymmetric B)
    (ht : ∀ i : Fin 6, ProperClassTable B i →
      ExcludedPair (orderMarkov B (order i)) (matrixPfaffian B ^ 2)) :
    ∀ p : CyclicOrder, ProperClass B p →
      ∀ C : Matrix 4, SkewSymmetric C → ConnectedSupport C →
        ∀ q : CyclicOrder, Topological C q →
          orderMarkov C q = orderMarkov B p →
          matrixPfaffian C ^ 2 = matrixPfaffian B ^ 2 → False := by
  intro p hp C hC hconn q hq hm hD
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have htab := (properClass_iff_table B hB p i hi).mp hp
  have hpair := ht i htab
  have hmi := ProperWiggleInvariants.markov_cyclic B hB p (order i) hi
  rw [← hmi] at hpair
  have hrec := ofSix_reconstruct (relabel C q) (relabel_skew C q hC)
  have hconnq := connected_relabel C q hconn
  rw [← hrec] at hconnq
  have hDq := ClassSeparation.pfaffian_square_relabel C hC q
  exact excluded_pair_no_topological _ _ _ _ _ _ _ _ hpair
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2
    hconnq hm (hDq.trans hD)

end QuiverProofs.ProperScalarTargets
