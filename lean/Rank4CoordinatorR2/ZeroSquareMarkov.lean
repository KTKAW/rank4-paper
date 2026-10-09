import Rank4Coordinator.HeightBound
import QuiverProofs.Algebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Uniform arithmetic for a zero-pivot square. No semantic MA/NMA or
unrestricted properness premise is manufactured here. Unit incident edges
are explicitly outside the lower-bound hypotheses. -/
namespace Rank4CoordinatorR2

def zeroMarkov (b c d e f : Int) : Int :=
  b*b + c*c + d*d + e*e + f*f - f*(b*c+d*e)

theorem zeroMarkov_eq (b c d e f : Int) :
    zeroMarkov b c d e f = QuiverProofs.Algebra.markov 0 b (-c) d (-e) f := by
  unfold zeroMarkov QuiverProofs.Algebra.markov QuiverProofs.Algebra.squareSum
    QuiverProofs.Algebra.cycleTerms
  ring

private theorem pair_square_bound (b c : Int) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    4*(b*b+c*c) - (b*c)*(b*c) ≤ 16 := by
  have hb2 : 0 ≤ b*b-4 := by nlinarith
  have hc2 : 0 ≤ c*c-4 := by nlinarith
  have hp := mul_nonneg hb2 hc2
  nlinarith [hp]

private theorem pair_product_bound (d e : Int) (hd : 2 ≤ d) (he : 2 ≤ e) :
    2*(d*d+e*e) ≤ (d*e)*(d*e) := by
  have hd2 : 0 ≤ d*d-4 := by nlinarith
  have he2 : 0 ≤ e*e-4 := by nlinarith
  have hp := mul_nonneg hd2 he2
  nlinarith [hp]

private theorem quadratic_band (u v p q f : Int)
    (hu : 4*u-p*p ≤ 16) (hv : 4*v ≤ 2*p*q) (hq : 4 ≤ q)
    (hl : p < 2*f) (hr : 2*f < p+2*q) :
    u+v+f*f-f*(p+q) < 3 := by
  have ht : 0 ≤ 2*f-p-1 := by omega
  have hs : 0 ≤ p+2*q-2*f-1 := by omega
  have hp := mul_nonneg ht hs
  have hts : 7 ≤ (2*f-p)*(p+2*q-2*f) := by nlinarith [hp]
  have hi : 4*(u+v+f*f-f*(p+q)) =
      (4*u-p*p)+(4*v-2*p*q)-(2*f-p)*(p+2*q-2*f) := by ring
  nlinarith [hi, hts]

theorem ordered_zero_band (b c d e f : Int)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hpq : d*e ≤ b*c) (hl : b*c < 2*f) (hr : 2*f < b*c+2*(d*e)) :
    zeroMarkov b c d e f < 3 := by
  have hq : 4 ≤ d*e := by
    have h := mul_nonneg (show 0 ≤ d-2 by omega) (show 0 ≤ e-2 by omega)
    nlinarith [h]
  have hprod : (d*e)*(d*e) ≤ (b*c)*(d*e) :=
    mul_le_mul_of_nonneg_right hpq (by omega)
  have hv : 4*(d*d+e*e) ≤ 2*(b*c)*(d*e) := by
    have h := pair_product_bound d e hd he
    nlinarith [hprod]
  simpa only [zeroMarkov, add_assoc] using
    quadratic_band (b*b+c*c) (d*d+e*e) (b*c) (d*e) f
      (pair_square_bound b c hb hc) hv hq hl hr

/-- An overflowing alternate square in this all-incident-at-least-two
cone forces the local scalar below three. This is an arithmetic conclusion,
not a theorem that every such matrix is NMA. -/
theorem zero_square_overflow_markov (b c d e f : Int) (H : Nat)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hf : (H:Int) < f)
    (h0lo : -(H:Int) ≤ f-b*c) (h0hi : f-b*c ≤ (H:Int))
    (h1lo : -(H:Int) ≤ f-d*e) (h1hi : f-d*e ≤ (H:Int))
    (hover : f+(H:Int) < b*c+d*e) :
    zeroMarkov b c d e f < 3 := by
  have hl0 : b*c < 2*f := by omega
  have hl1 : d*e < 2*f := by omega
  have hr0 : 2*f < b*c+2*(d*e) := by omega
  have hr1 : 2*f < d*e+2*(b*c) := by omega
  rcases le_total (d*e) (b*c) with hpq | hqp
  · exact ordered_zero_band b c d e f hb hc hd he hpq hl0 hr0
  · have h := ordered_zero_band d e b c f hd he hb hc hqp hl1 hr1
    simpa [zeroMarkov, add_comm, add_left_comm, add_assoc] using h

/-- The exact scalar consumer for the square reroute. Its scalar hypothesis
is visible; connecting it to semantic MA is a separate obligation. -/
theorem zero_square_guard_of_markov (b c d e f : Int) (H : Nat)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hf : (H:Int) < f)
    (h0lo : -(H:Int) ≤ f-b*c) (h0hi : f-b*c ≤ (H:Int))
    (h1lo : -(H:Int) ≤ f-d*e) (h1hi : f-d*e ≤ (H:Int))
    (hm : 3 ≤ zeroMarkov b c d e f) :
    -(H:Int) ≤ f-b*c-d*e ∧ f-b*c-d*e ≤ (H:Int) := by
  have hq : 0 ≤ d*e := mul_nonneg (by omega) (by omega)
  constructor
  · by_contra h
    have hover : f+(H:Int) < b*c+d*e := by omega
    have hn := zero_square_overflow_markov b c d e f H hb hc hd he hf
      h0lo h0hi h1lo h1hi hover
    omega
  · omega

#print axioms ordered_zero_band
#print axioms zeroMarkov_eq
#print axioms zero_square_overflow_markov
#print axioms zero_square_guard_of_markov
end Rank4CoordinatorR2
