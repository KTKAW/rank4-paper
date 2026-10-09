import QuiverProofs.Algebra

namespace QuiverProofs.FirstGap
open Algebra

/-- For the six edges 01,02,03,12,13,23, every nontrivial vertex cut
contains a nonzero edge. The seven clauses list all cuts up to complement;
thus this is connectedness of the underlying four-vertex support graph. -/
def Connected (a b c d e f : Int) : Prop :=
  (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
  (a ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) ∧
  (b ≠ 0 ∨ d ≠ 0 ∨ f ≠ 0) ∧
  (c ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0) ∧
  (b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) ∧
  (a ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ f ≠ 0) ∧
  (a ≠ 0 ∨ b ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0)

/-- All twelve possible labeled weighted paths: their two disjoint end
edges have weight t, and the unique joining edge has weight 1. -/
def WeightedPath (a b c d e f : Int) (t : Int) : Prop :=
  (a=t ∧ f=t ∧ ((b=1 ∧ c=0 ∧ d=0 ∧ e=0) ∨
    (b=0 ∧ c=1 ∧ d=0 ∧ e=0) ∨ (b=0 ∧ c=0 ∧ d=1 ∧ e=0) ∨
    (b=0 ∧ c=0 ∧ d=0 ∧ e=1))) ∨
  (b=t ∧ e=t ∧ ((a=1 ∧ c=0 ∧ d=0 ∧ f=0) ∨
    (a=0 ∧ c=1 ∧ d=0 ∧ f=0) ∨ (a=0 ∧ c=0 ∧ d=1 ∧ f=0) ∨
    (a=0 ∧ c=0 ∧ d=0 ∧ f=1))) ∨
  (c=t ∧ d=t ∧ ((a=1 ∧ b=0 ∧ e=0 ∧ f=0) ∨
    (a=0 ∧ b=1 ∧ e=0 ∧ f=0) ∨ (a=0 ∧ b=0 ∧ e=1 ∧ f=0) ∨
    (a=0 ∧ b=0 ∧ e=0 ∧ f=1)))

/-- In a topological order this is exactly the unit four-cycle consisting
of a directed three-edge path and its source-to-sink shortcut. -/
def UnitFourCycle (a b c d e f : Int) : Prop :=
  a=1 ∧ b=0 ∧ c=1 ∧ d=1 ∧ e=0 ∧ f=1

theorem connected_not_matching (a b c d e f : Int)
    (h : Connected a b c d e f) : ¬ MatchingSupport a b c d e f := by
  unfold Connected at h
  unfold MatchingSupport
  omega

theorem connected_strict_pfaffian_bound (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (h : Connected a b c d e f) :
    2 * (pfaffian a b c d e f).natAbs < markov a b c d e f :=
  strict_pfaffian_bound_of_not_matching a b c d e f ha hb hc hd he hf
    (connected_not_matching a b c d e f h)

private theorem square_le_one (x : Int) (h : x^2 ≤ 1) :
    x = -1 ∨ x=0 ∨ x=1 := by
  by_cases hp : 2 ≤ x
  · have := square_monotone 2 x (by decide) hp
    omega
  · by_cases hn : x ≤ -2
    · have := square_monotone 2 (-x) (by decide) (by omega)
      have heq : (-x)^2 = x^2 := by grind
      omega
    · omega

private theorem square_one (x : Int) (h : x^2=1) : x = -1 ∨ x=1 := by
  have := square_le_one x (by omega)
  grind

private theorem product_one (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x*y=1) : x=1 ∧ y=1 := by
  by_cases hzero : x=0
  · simp [hzero] at h
  · by_cases hzero' : y=0
    · simp [hzero'] at h
    · have hx' : 1 ≤ x := by omega
      have hy' : 1 ≤ y := by omega
      have h₁ := Int.mul_le_mul hx' (Int.le_refl y) hy hx
      have h₂ := Int.mul_le_mul (Int.le_refl x) hy' (by decide) hx
      grind

private theorem unit_sum (x y z t : Int) (ht : 0 ≤ t)
    (h : x^2+y^2+z^2+t=1) :
    (x=0 ∧ y=0 ∧ z=0 ∧ t=1) ∨
    ((x = -1 ∨ x=1) ∧ y=0 ∧ z=0 ∧ t=0) ∨
    (x=0 ∧ (y = -1 ∨ y=1) ∧ z=0 ∧ t=0) ∨
    (x=0 ∧ y=0 ∧ (z = -1 ∨ z=1) ∧ t=0) := by
  have hx := square_nonnegative x
  have hy := square_nonnegative y
  have hz := square_nonnegative z
  by_cases hx0 : x^2=0
  · have ex := square_eq_zero x hx0
    by_cases hy0 : y^2=0
    · have ey := square_eq_zero y hy0
      by_cases hz0 : z^2=0
      · have ez := square_eq_zero z hz0
        left; omega
      · right; right; right
        exact ⟨ex, ey, square_one z (by omega), by omega⟩
    · right; right; left
      exact ⟨ex, square_one y (by omega), square_eq_zero z (by omega), by omega⟩
  · right; left
    exact ⟨square_one x (by omega), square_eq_zero y (by omega),
      square_eq_zero z (by omega), by omega⟩

private theorem positive_gap_classification (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : Connected a b c d e f)
    (hgap : markov a b c d e f - 2*pfaffian a b c d e f=1) :
    (∃ t : Int, 1 ≤ t ∧ WeightedPath a b c d e f t) ∨
      UnitFourCycle a b c d e f := by
  have ht := cycleTerms_nonnegative a b c d e f ha hb hc hd he hf
  have hid := gap_positive_identity a b c d e f
  have hh := unit_sum (a-f) (b+e) (c-d) (cycleTerms a b c d e f) ht (by omega)
  unfold Connected at hconn
  rcases hh with hzero | hfirst | hsecond | hthird
  · obtain ⟨haf,hbe,hcd,htone⟩ := hzero
    have bz : b=0 := by omega
    have ez : e=0 := by omega
    have hprod : (a*c)^2=1 := by unfold cycleTerms at htone; grind
    have hac : 0 ≤ a*c := Int.mul_nonneg ha hc
    have hone : a*c=1 := by have := square_one (a*c) hprod; omega
    have := product_one a c ha hc hone
    right; unfold UnitFourCycle; omega
  · obtain ⟨haf,hbe,hcd,htzero⟩ := hfirst
    have bz : b=0 := by omega
    have ez : e=0 := by omega
    have cpos : 1 ≤ c := by omega
    have hprod : (a*f)*(c*c)=0 := by unfold cycleTerms at htzero; grind
    have hcprod : c*c ≠ 0 := by
      intro hz
      have := Int.mul_eq_zero.mp hz
      omega
    have hafzero : a*f=0 := (Int.mul_eq_zero.mp hprod).resolve_right hcprod
    have hor := Int.mul_eq_zero.mp hafzero
    left; refine ⟨c,cpos,?_⟩
    unfold WeightedPath
    right; right
    clear hconn
    omega
  · obtain ⟨haf,hbe,hcd,htzero⟩ := hsecond
    have hbeone : b+e=1 := by omega
    have hac := Int.mul_nonneg ha hc
    have hs := square_nonnegative (a*c)
    have hprod : 2*(a*c)+(a*c)^2=0 := by
      unfold cycleTerms at htzero
      grind
    have haczero : a*c=0 := by omega
    cases Int.mul_eq_zero.mp haczero with
    | inl az =>
      left; refine ⟨c,by omega,?_⟩
      unfold WeightedPath
      right; right
      clear hconn
      omega
    | inr cz =>
      left; refine ⟨a,by omega,?_⟩
      unfold WeightedPath
      left
      clear hconn
      omega
  · obtain ⟨haf,hbe,hcd,htzero⟩ := hthird
    have bz : b=0 := by omega
    have ez : e=0 := by omega
    have apos : 1 ≤ a := by omega
    have hprod : (c*d)*(a*a)=0 := by unfold cycleTerms at htzero; grind
    have haprod : a*a ≠ 0 := by
      intro hz
      have := Int.mul_eq_zero.mp hz
      omega
    have hcdzero : c*d=0 := (Int.mul_eq_zero.mp hprod).resolve_right haprod
    have hor := Int.mul_eq_zero.mp hcdzero
    left; refine ⟨a,apos,?_⟩
    unfold WeightedPath
    left
    clear hconn
    omega

private theorem negative_gap_classification (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : Connected a b c d e f)
    (hgap : markov a b c d e f + 2*pfaffian a b c d e f=1) :
    ∃ t : Int, 1 ≤ t ∧ WeightedPath a b c d e f t := by
  have ht := cycleTerms_nonnegative a b c d e f ha hb hc hd he hf
  have hid := gap_negative_identity a b c d e f
  have hh := unit_sum (a+f) (b-e) (c+d) (cycleTerms a b c d e f) ht (by omega)
  unfold Connected at hconn
  rcases hh with hzero | hfirst | hsecond | hthird
  · obtain ⟨haf,hbe,hcd,htone⟩ := hzero
    omega
  · obtain ⟨haf,hbe,hcd,htzero⟩ := hfirst
    refine ⟨b,by omega,?_⟩
    unfold WeightedPath
    right; left
    clear hconn
    omega
  · obtain ⟨haf,hbe,hcd,htzero⟩ := hsecond
    omega
  · obtain ⟨haf,hbe,hcd,htzero⟩ := hthird
    refine ⟨b,by omega,?_⟩
    unfold WeightedPath
    right; left
    clear hconn
    omega

/-- Full first-gap support classification in nonnegative topological
coordinates, for every weight (no finite search or size bound). -/
theorem first_gap_classification (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : Connected a b c d e f)
    (hgap : markov a b c d e f = 2*(pfaffian a b c d e f).natAbs+1) :
    (∃ t : Int, 1 ≤ t ∧ WeightedPath a b c d e f t) ∨
      UnitFourCycle a b c d e f := by
  cases Int.le_total 0 (pfaffian a b c d e f) with
  | inl hp =>
    rw [Int.natAbs_of_nonneg hp] at hgap
    exact positive_gap_classification a b c d e f ha hb hc hd he hf hconn (by omega)
  | inr hp =>
    rw [Int.ofNat_natAbs_of_nonpos hp] at hgap
    exact Or.inl (negative_gap_classification a b c d e f ha hb hc hd he hf hconn (by omega))

/-- Every labeled path has the claimed invariants, independently of its
orientation in the chosen topological order. -/
theorem weighted_path_invariants (a b c d e f t : Int)
    (h : WeightedPath a b c d e f t) :
    markov a b c d e f = 2*t^2+1 ∧
    (pfaffian a b c d e f = t^2 ∨ pfaffian a b c d e f = -t^2) := by
  unfold WeightedPath at h
  unfold markov squareSum cycleTerms pfaffian
  grind

theorem weighted_path_absolute_pfaffian (a b c d e f t : Int)
    (h : WeightedPath a b c d e f t) :
    ((pfaffian a b c d e f).natAbs : Int) = t^2 := by
  have hp := (weighted_path_invariants a b c d e f t h).2
  have ht := square_nonnegative t
  cases hp with
  | inl hp => rw [hp, Int.natAbs_of_nonneg ht]
  | inr hp =>
    rw [hp, Int.ofNat_natAbs_of_nonpos (show -t^2 ≤ 0 by omega)]
    omega

theorem weighted_path_connected (a b c d e f t : Int)
    (ht : 1 ≤ t) (h : WeightedPath a b c d e f t) :
    Connected a b c d e f := by
  unfold WeightedPath at h
  unfold Connected
  grind (splits := 20)

theorem weighted_path_unit_gap (a b c d e f t : Int)
    (h : WeightedPath a b c d e f t) :
    markov a b c d e f = 2*(pfaffian a b c d e f).natAbs+1 := by
  have hm := (weighted_path_invariants a b c d e f t h).1
  have hp := weighted_path_absolute_pfaffian a b c d e f t h
  omega

theorem unit_four_cycle_unit_gap (a b c d e f : Int)
    (h : UnitFourCycle a b c d e f) :
    markov a b c d e f = 2*(pfaffian a b c d e f).natAbs+1 := by
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := h
  decide

/-- The manuscript's exact first-gap equivalence, with path and cycle
shapes expanded as explicit labeled support graphs. -/
theorem first_gap_iff (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : Connected a b c d e f) :
    markov a b c d e f = 2*(pfaffian a b c d e f).natAbs+1 ↔
    (∃ t : Int, 1 ≤ t ∧ WeightedPath a b c d e f t) ∨
      UnitFourCycle a b c d e f := by
  constructor
  · exact first_gap_classification a b c d e f ha hb hc hd he hf hconn
  · intro h
    cases h with
    | inl h =>
      obtain ⟨t,_,h⟩ := h
      exact weighted_path_unit_gap a b c d e f t h
    | inr h => exact unit_four_cycle_unit_gap a b c d e f h

/-- Necessary Pfaffian values on the first gap; this is the complete
unbounded arithmetic exclusion used by the infinite-family argument. -/
theorem first_gap_pfaffian_values (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : Connected a b c d e f)
    (hgap : markov a b c d e f = 2*(pfaffian a b c d e f).natAbs+1) :
    ((pfaffian a b c d e f).natAbs : Int) = 2 ∨
      ∃ t : Int, 1 ≤ t ∧ ((pfaffian a b c d e f).natAbs : Int) = t^2 := by
  have h := first_gap_classification a b c d e f ha hb hc hd he hf hconn hgap
  cases h with
  | inl h =>
    obtain ⟨t,ht,h⟩ := h
    exact Or.inr ⟨t,ht,weighted_path_absolute_pfaffian a b c d e f t h⟩
  | inr h =>
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := h
    left; decide

/-- No nonnegative connected acyclic tuple has the invariant pair of
q_s. Mutation-class transport is a separate structural step. -/
theorem family_no_acyclic_invariant_representative (s a b c d e f : Int)
    (hs : 1 ≤ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : Connected a b c d e f)
    (hm : markov a b c d e f =
      markov 0 0 (familyC s) (familyD s) (-1) 1)
    (hp : ((pfaffian a b c d e f).natAbs : Int) = familyP s) : False := by
  have hg := family_unit_gap s
  have hgap : markov a b c d e f = 2*(pfaffian a b c d e f).natAbs+1 := by omega
  have hvalues := first_gap_pfaffian_values a b c d e f ha hb hc hd he hf hconn hgap
  have hexcluded := family_excludes_first_gap_values s hs
  cases hvalues with
  | inl h => exact hexcluded.1 (by omega)
  | inr h =>
    obtain ⟨t,ht,h⟩ := h
    exact hexcluded.2 ⟨t,ht,by omega⟩

end QuiverProofs.FirstGap
