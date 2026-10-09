import Lean

/-!
Elementary integer algebra from `rank4_general_research/technical_note.tex`.

The six arguments are the ordered upper entries (a,b,c,d,e,f).
`markov` is the manuscript's explicit polynomial, and the Alexander
determinant expansion is proved directly below. Transport of this value
along proper mutations is not asserted by this module.
-/

namespace QuiverProofs.Algebra

def pfaffian (a b c d e f : Int) : Int := a*f - b*e + c*d

def squareSum (a b c d e f : Int) : Int :=
  a^2 + b^2 + c^2 + d^2 + e^2 + f^2

def cycleTerms (a b c d e f : Int) : Int :=
  a*b*d + a*c*e + b*c*f + d*e*f + a*c*d*f

def markov (a b c d e f : Int) : Int :=
  squareSum a b c d e f + cycleTerms a b c d e f

/-- The three-by-three determinant, written by cofactor expansion. -/
def det3 (a b c d e f g h i : Int) : Int :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

/-- The four-by-four determinant, by cofactor expansion in the first row.
Arguments are in row-major order. This explicit definition keeps the proof
independent of an external matrix library. -/
def det4 (a b c d e f g h i j k l m n o p : Int) : Int :=
  a * det3 f g h j k l n o p -
  b * det3 e g h i k l m o p +
  c * det3 e f h i j l m n p -
  d * det3 e f g i j k m n o

theorem skew_determinant_is_pfaffian_square (a b c d e f : Int) :
    det4 0 a b c (-a) 0 d e (-b) (-d) 0 f (-c) (-e) (-f) 0 =
      (pfaffian a b c d e f)^2 := by
  unfold det4 det3 pfaffian
  grind

/-- Exact Alexander determinant expansion for U with diagonal 1 and upper
entries (-a,-b,-c,-d,-e,-f), valid at every integer t. -/
theorem alexander_determinant_expansion (a b c d e f t : Int) :
    det4 (t-1) (-t*a) (-t*b) (-t*c)
      a (t-1) (-t*d) (-t*e)
      b d (t-1) (-t*f)
      c e f (t-1) =
    (t-1)^4 + markov a b c d e f * t * (t-1)^2 +
      (pfaffian a b c d e f)^2*t^2 := by
  unfold det4 det3 markov squareSum cycleTerms pfaffian
  grind

/-- The symmetric-companion determinant adds no new scalar to M and D. -/
theorem symmetric_companion_determinant (a b c d e f : Int) :
    det4 2 (-a) (-b) (-c) (-a) 2 (-d) (-e)
      (-b) (-d) 2 (-f) (-c) (-e) (-f) 2 =
      16 - 4*markov a b c d e f + (pfaffian a b c d e f)^2 := by
  unfold det4 det3 markov squareSum cycleTerms pfaffian
  grind

/-- The positive-Pfaffian sum-of-squares identity (*). -/
theorem gap_positive_identity (a b c d e f : Int) :
    markov a b c d e f - 2 * pfaffian a b c d e f =
    (a-f)^2 + (b+e)^2 + (c-d)^2 + cycleTerms a b c d e f := by
  unfold markov squareSum pfaffian
  grind

/-- The negative-Pfaffian sum-of-squares identity (**). -/
theorem gap_negative_identity (a b c d e f : Int) :
    markov a b c d e f + 2 * pfaffian a b c d e f =
    (a+f)^2 + (b-e)^2 + (c+d)^2 + cycleTerms a b c d e f := by
  unfold markov squareSum pfaffian
  grind

/-- The quadratic in the last coordinate used by finite candidate enumeration. -/
theorem last_coordinate_quadratic (a b c d e f m : Int) :
    markov a b c d e f - m =
    f^2 + (b*c+d*e+a*c*d)*f +
      (a^2+b^2+c^2+d^2+e^2+a*b*d+a*c*e-m) := by
  unfold markov squareSum cycleTerms
  grind

theorem square_nonnegative (x : Int) : 0 ≤ x^2 := by
  cases Int.le_total 0 x with
  | inl h => exact Int.pow_nonneg h
  | inr h =>
    have hmul := Int.mul_nonneg_of_nonpos_of_nonpos h h
    grind

theorem square_eq_zero (x : Int) (h : x^2 = 0) : x = 0 := by
  have hmul : x*x = 0 := by grind
  exact (Int.mul_eq_zero.mp hmul).elim id id

theorem cycleTerms_nonnegative (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 ≤ cycleTerms a b c d e f := by
  have h₁ := Int.mul_nonneg (Int.mul_nonneg ha hb) hd
  have h₂ := Int.mul_nonneg (Int.mul_nonneg ha hc) he
  have h₃ := Int.mul_nonneg (Int.mul_nonneg hb hc) hf
  have h₄ := Int.mul_nonneg (Int.mul_nonneg hd he) hf
  have h₅ := Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg ha hc) hd) hf
  unfold cycleTerms
  omega

/-- Every nonnegative topological tuple satisfies S ≤ M. -/
theorem squareSum_le_markov (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    squareSum a b c d e f ≤ markov a b c d e f := by
  have := cycleTerms_nonnegative a b c d e f ha hb hc hd he hf
  unfold markov
  omega

/-- The non-strict Pfaffian bound for every nonnegative ordered tuple. -/
theorem pfaffian_bound (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    2 * (pfaffian a b c d e f).natAbs ≤ markov a b c d e f := by
  have ht := cycleTerms_nonnegative a b c d e f ha hb hc hd he hf
  cases Int.le_total 0 (pfaffian a b c d e f) with
  | inl hp =>
    have hid := gap_positive_identity a b c d e f
    have h₁ := square_nonnegative (a-f)
    have h₂ := square_nonnegative (b+e)
    have h₃ := square_nonnegative (c-d)
    rw [Int.natAbs_of_nonneg hp]
    omega
  | inr hp =>
    have hid := gap_negative_identity a b c d e f
    have h₁ := square_nonnegative (a+f)
    have h₂ := square_nonnegative (b-e)
    have h₃ := square_nonnegative (c+d)
    rw [Int.ofNat_natAbs_of_nonpos hp]
    omega

/-- All possibly nonzero entries belong to one pair of disjoint edges. -/
def MatchingSupport (a b c d e f : Int) : Prop :=
  (b=0 ∧ c=0 ∧ d=0 ∧ e=0) ∨
  (a=0 ∧ c=0 ∧ d=0 ∧ f=0) ∨
  (a=0 ∧ b=0 ∧ e=0 ∧ f=0)

/-- Equality in the Pfaffian bound forces a disjoint matching support. -/
theorem equality_forces_matching (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (heq : markov a b c d e f = 2 * (pfaffian a b c d e f).natAbs) :
    MatchingSupport a b c d e f := by
  have ht := cycleTerms_nonnegative a b c d e f ha hb hc hd he hf
  cases Int.le_total 0 (pfaffian a b c d e f) with
  | inl hp =>
    rw [Int.natAbs_of_nonneg hp] at heq
    have hid := gap_positive_identity a b c d e f
    have h₁ := square_nonnegative (a-f)
    have h₂ := square_nonnegative (b+e)
    have h₃ := square_nonnegative (c-d)
    have haf := square_eq_zero (a-f) (by omega)
    have hbe := square_eq_zero (b+e) (by omega)
    have hcd := square_eq_zero (c-d) (by omega)
    have htzero : cycleTerms a b c d e f = 0 := by omega
    have hprod : (a*c)^2 = 0 := by
      unfold cycleTerms at htzero
      have hbzero : b=0 := by omega
      have hezero : e=0 := by omega
      grind
    have hac := square_eq_zero (a*c) hprod
    unfold MatchingSupport
    cases Int.mul_eq_zero.mp hac with
    | inl hazero => right; right; omega
    | inr hczero => left; omega
  | inr hp =>
    rw [Int.ofNat_natAbs_of_nonpos hp] at heq
    have hid := gap_negative_identity a b c d e f
    have h₁ := square_nonnegative (a+f)
    have h₂ := square_nonnegative (b-e)
    have h₃ := square_nonnegative (c+d)
    have haf := square_eq_zero (a+f) (by omega)
    have hcd := square_eq_zero (c+d) (by omega)
    unfold MatchingSupport
    right; left; omega

/-- The strict bound under the explicit algebraic hypothesis excluding matchings.
A connected four-vertex support excludes matchings; that graph-level implication
is separate from this arithmetic statement. -/
theorem strict_pfaffian_bound_of_not_matching (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hconn : ¬ MatchingSupport a b c d e f) :
    2 * (pfaffian a b c d e f).natAbs < markov a b c d e f := by
  have hbound := pfaffian_bound a b c d e f ha hb hc hd he hf
  by_cases heq : markov a b c d e f = 2 * (pfaffian a b c d e f).natAbs
  · exact False.elim (hconn (equality_forces_matching a b c d e f ha hb hc hd he hf heq))
  · omega

/-- Explicit coordinate-square bounds justify a finite search at fixed M. -/
theorem coordinate_squares_le_markov (a b c d e f : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    a^2 ≤ markov a b c d e f ∧ b^2 ≤ markov a b c d e f ∧
    c^2 ≤ markov a b c d e f ∧ d^2 ≤ markov a b c d e f ∧
    e^2 ≤ markov a b c d e f ∧ f^2 ≤ markov a b c d e f := by
  have hbound := squareSum_le_markov a b c d e f ha hb hc hd he hf
  have h₁ := square_nonnegative a
  have h₂ := square_nonnegative b
  have h₃ := square_nonnegative c
  have h₄ := square_nonnegative d
  have h₅ := square_nonnegative e
  have h₆ := square_nonnegative f
  unfold squareSum at hbound
  omega

/-- The finite-candidate quadratic is strictly increasing for f ≥ 0. -/
theorem last_coordinate_strictly_increasing (a b c d e f g : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) (hfg : f < g) :
    markov a b c d e f < markov a b c d e g := by
  have hbc := Int.mul_nonneg hb hc
  have hde := Int.mul_nonneg hd he
  have hacd := Int.mul_nonneg (Int.mul_nonneg ha hc) hd
  have h₁ : 0 < g-f := by omega
  have h₂ : 0 < g+f+(b*c+d*e+a*c*d) := by omega
  have hprod := Int.mul_pos h₁ h₂
  have hid : markov a b c d e g - markov a b c d e f =
      (g-f)*(g+f+(b*c+d*e+a*c*d)) := by
    unfold markov squareSum cycleTerms
    grind
  omega

/-- At most one nonnegative last coordinate has the requested invariant. -/
theorem last_coordinate_unique (a b c d e f g : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (heq : markov a b c d e f = markov a b c d e g) : f = g := by
  by_cases hfg : f < g
  · have := last_coordinate_strictly_increasing a b c d e f g ha hb hc hd he hf hfg
    omega
  · by_cases hgf : g < f
    · have := last_coordinate_strictly_increasing a b c d e g f ha hb hc hd he hg hgf
      omega
    · omega

/-- Polynomial invariants of one topological orientation of the weighted path. -/
theorem weighted_path_invariants (t : Int) :
    markov t 0 0 1 0 t = 2*t^2+1 ∧ pfaffian t 0 0 1 0 t = t^2 := by
  unfold markov squareSum cycleTerms pfaffian
  grind

/-- The exceptional unit four-cycle on the first gap. -/
theorem unit_four_cycle_invariants :
    markov 1 0 1 1 0 1 = 5 ∧ pfaffian 1 0 1 1 0 1 = 2 := by
  decide

def familyC (s : Int) : Int := s^2+s+1
def familyD (s : Int) : Int := s^2+1
def familyP (s : Int) : Int := familyC s * familyD s

/-- The exact polynomial Pfaffian of q_s (before taking absolute value). -/
theorem family_pfaffian (s : Int) :
    pfaffian 0 0 (familyC s) (familyD s) (-1) 1 = familyP s := by
  unfold pfaffian familyP
  grind

/-- The unique-order M formula asserted in the infinite-family proof. -/
theorem family_markov (s : Int) :
    markov 0 0 (familyC s) (familyD s) (-1) 1 =
      (familyC s)^2 + (familyD s)^2 + 2 - familyD s := by
  unfold markov squareSum cycleTerms
  grind

/-- All integer parameters, not merely sampled parameters, give unit gap. -/
theorem family_unit_gap (s : Int) :
    markov 0 0 (familyC s) (familyD s) (-1) 1 - 2*familyP s = 1 := by
  unfold markov squareSum cycleTerms familyP familyC familyD
  grind

/-- The even-parameter lower square gap, with s = 2k and X = s²+s/2. -/
theorem even_lower_square_gap (k : Int) :
    familyP (2*k) - (4*k^2+k)^2 = 7*k^2+2*k+1 := by
  unfold familyP familyC familyD
  grind

/-- The even-parameter upper square gap. -/
theorem even_upper_square_gap (k : Int) :
    (4*k^2+k+1)^2 - familyP (2*k) = k^2 := by
  unfold familyP familyC familyD
  grind

/-- The odd-parameter lower square gap, with s = 2k+1 and X = s²+(s+1)/2. -/
theorem odd_lower_square_gap (k : Int) :
    familyP (2*k+1) - (4*k^2+5*k+2)^2 = 3*k^2+4*k+2 := by
  unfold familyP familyC familyD
  grind

/-- The odd-parameter upper square gap. -/
theorem odd_upper_square_gap (k : Int) :
    (4*k^2+5*k+3)^2 - familyP (2*k+1) = 5*k^2+6*k+3 := by
  unfold familyP familyC familyD
  grind

theorem square_monotone (x y : Int) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x^2 ≤ y^2 := by
  have h := Int.mul_le_mul hxy hxy hx (Int.le_trans hx hxy)
  grind

/-- No integer square lies strictly between successive nonnegative squares. -/
theorem not_square_between_consecutive (p x : Int) (hx : 0 ≤ x)
    (hlower : x^2 < p) (hupper : p < (x+1)^2) :
    ¬ ∃ y : Int, y^2 = p := by
  intro ⟨y, hy⟩
  have hn : 0 ≤ (y.natAbs : Int) := by omega
  have hsq := Int.natAbs_pow_two y
  cases Int.le_total (y.natAbs : Int) x with
  | inl h =>
    have := square_monotone (y.natAbs : Int) x hn h
    omega
  | inr h =>
    by_cases heq : (y.natAbs : Int) = x
    · have : y^2 = x^2 := by grind
      omega
    · have hstep : x+1 ≤ (y.natAbs : Int) := by omega
      have := square_monotone (x+1) (y.natAbs : Int) (by omega) hstep
      omega

theorem family_even_between_squares (k : Int) (hk : 1 ≤ k) :
    (4*k^2+k)^2 < familyP (2*k) ∧
    familyP (2*k) < (4*k^2+k+1)^2 := by
  have hlow := even_lower_square_gap k
  have hupp := even_upper_square_gap k
  have hpos := Int.mul_pos (show 0 < k by omega) (show 0 < k by omega)
  have hsq : 0 < k^2 := by grind
  omega

theorem family_odd_between_squares (k : Int) (hk : 0 ≤ k) :
    (4*k^2+5*k+2)^2 < familyP (2*k+1) ∧
    familyP (2*k+1) < (4*k^2+5*k+3)^2 := by
  have hlow := odd_lower_square_gap k
  have hupp := odd_upper_square_gap k
  have hsq := square_nonnegative k
  omega

/-- The nonsquare step of the infinite-family proof for every integer s ≥ 1. -/
theorem family_pfaffian_not_square (s : Int) (hs : 1 ≤ s) :
    ¬ ∃ y : Int, y^2 = familyP s := by
  have hparity : s = 2*(s/2) ∨ s = 2*(s/2)+1 := by omega
  cases hparity with
  | inl heven =>
    have hk : 1 ≤ s/2 := by omega
    have hbounds := family_even_between_squares (s/2) hk
    have hsq := square_nonnegative (s/2)
    have hx : 0 ≤ 4*(s/2)^2+s/2 := by omega
    rw [heven]
    exact not_square_between_consecutive _ _ hx hbounds.1 hbounds.2
  | inr hodd =>
    have hk : 0 ≤ s/2 := by omega
    have hbounds := family_odd_between_squares (s/2) hk
    have hsq := square_nonnegative (s/2)
    have hx : 0 ≤ 4*(s/2)^2+5*(s/2)+2 := by omega
    rw [hodd]
    apply not_square_between_consecutive _ _ hx hbounds.1
    grind

theorem family_pfaffian_at_least_six (s : Int) (hs : 1 ≤ s) :
    6 ≤ familyP s := by
  have hsquare := square_monotone 1 s (by decide) hs
  have hc : 3 ≤ familyC s := by unfold familyC; omega
  have hd : 2 ≤ familyD s := by unfold familyD; omega
  have hprod := Int.mul_le_mul hc hd (by decide) (show 0 ≤ familyC s by omega)
  unfold familyP
  omega

theorem family_absolute_pfaffian (s : Int) (hs : 1 ≤ s) :
    ((pfaffian 0 0 (familyC s) (familyD s) (-1) 1).natAbs : Int) = familyP s := by
  rw [family_pfaffian]
  have := family_pfaffian_at_least_six s hs
  exact Int.natAbs_of_nonneg (by omega)

/-- The arithmetic invariant pair cannot occur among the listed first-gap types.
This does not itself assert mutation non-acyclicity: that additionally needs
proper-order transport and the full graph-theoretic first-gap classification. -/
theorem family_excludes_first_gap_values (s : Int) (hs : 1 ≤ s) :
    familyP s ≠ 2 ∧ ¬ ∃ t : Int, 1 ≤ t ∧ familyP s = t^2 := by
  have hlarge := family_pfaffian_at_least_six s hs
  have hnonsquare := family_pfaffian_not_square s hs
  constructor
  · omega
  · intro ⟨t, _, ht⟩
    exact hnonsquare ⟨t, ht.symm⟩

end QuiverProofs.Algebra
