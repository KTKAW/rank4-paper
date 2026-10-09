import Rank4Round2.UnitMarkov

/-! The remaining d=1/c=1 incident-unit arithmetic boundary. The canonical
Pfaffian comparison is proved from exact child sum bounds and overflow;
no semantic MA/Pfaffian bridge is asserted.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

def unitPfaffian (b c d e f : Int) : Int := f+b*e-c*d

theorem unitPfaffian_eq (b c d e f : Int) :
    unitPfaffian b c d e f = Algebra.pfaffian 1 b (-c) d (-e) f := by
  unfold unitPfaffian Algebra.pfaffian
  ring

private theorem product_lower (f z L : Int) (hf : L≤f) (hz : L≤z) :
    L*(f+z-L+2)≤f*(z+2) := by
  have hp := mul_nonneg (show 0≤f-L by omega) (show 0≤z-L by omega)
  nlinarith [hp]

private theorem d_one_ordered_y (b c e : Int)
    (hb : 2≤b) (hc : 2≤c) (he : 1≤e)
    (hy : b+1≤c+e) (hT : 2*(c+e)+2≤b*c+c+e) :
    2+b*b+b+c*c+e*e+c*e-2*b*e+2*c
      -(c+e+1)*(b*c+1)≤-6 := by
  have hA := mul_nonneg (show 0≤e by omega)
    (show 0≤(b-1)*c-e-2 by nlinarith [hT])
  have hCpoly : 0≤c*c-c-2 := by
    have h := mul_nonneg (show 0≤c-2 by omega) (show 0≤c+1 by omega)
    nlinarith [h]
  have hB := mul_nonneg (show 0≤b-1 by omega) hCpoly
  have hC := mul_nonneg (show 0≤b-1 by omega) (show 0≤c+e-b-1 by omega)
  have hb2 : 4≤b*b := by nlinarith
  have hid :
      2+b*b+b+c*c+e*e+c*e-2*b*e+2*c-(c+e+1)*(b*c+1) =
      5-b*b-b-5*e-e*((b-1)*c-e-2)-(b-1)*(c*c-c-2)
        -2*((b-1)*(c+e-b-1)) := by ring
  rw [hid]
  omega

private theorem d_one_ordered_x (b c e : Int)
    (hb : 2≤b) (hc : 2≤c) (he : 1≤e) (hy : c+e≤b+1) :
    2+b*b+b+c*c+e*e+c*e-2*b*e+2*c
      -(b+2)*(b*c+c+e-b)≤-5 := by
  have hA := mul_nonneg (show 0≤e by omega) (show 0≤b+1-c-e by omega)
  have hB := mul_nonneg (show 0≤c by omega) (show 0≤b-c by omega)
  have hC := mul_nonneg (show 0≤c-2 by omega) (sq_nonneg b)
  have hD := mul_nonneg (show 0≤2*b by omega) (show 0≤c+e-3 by omega)
  have hid :
      2+b*b+b+c*c+e*e+c*e-2*b*e+2*c-(b+2)*(b*c+c+e-b) =
      2-3*b-e-e*(b+1-c-e)-c*(b-c)-(c-2)*(b*b)-2*b*(c+e-3) := by ring
  have hC' : 0≤(c-2)*(b*b) := by simpa only [pow_two] using hC
  rw [hid]
  omega

/-- In the d=1 overflowing unit boundary the scalar is below twice the
positive canonical Pfaffian, uniformly over arbitrary integer weights. -/
theorem d_one_overflow_pfaffian (b c e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (he : 0<e)
    (hbd : b+1≤(H:Int)) (hce : c+e≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<unitCost b c 1 e) :
    0<unitPfaffian b c 1 e f ∧
      unitMarkov b c 1 e f-2*unitPfaffian b c 1 e f≤-5 := by
  have hcost : unitCost b c 1 e=b*c+c+e := by unfold unitCost; ring
  have hb2 : 2≤b := by
    by_contra h
    have hb1 : b=1 := by omega
    rw [hcost,hb1] at hover
    simp only [one_mul] at hover
    omega
  have hc2 : 2≤c := by
    by_contra h
    have hc1 : c=1 := by omega
    rw [hcost,hc1] at hover
    simp only [mul_one] at hover
    omega
  have hpf : 0<unitPfaffian b c 1 e f := by
    have hbe := mul_pos hb he
    unfold unitPfaffian
    nlinarith [hbe]
  refine ⟨hpf,?_⟩
  have hM : unitMarkov b c 1 e f-2*unitPfaffian b c 1 e f =
      2+b*b+b+c*c+e*e+c*e-2*b*e+2*c-f*(unitCost b c 1 e-f+2) := by
    unfold unitMarkov unitPfaffian unitCost
    ring
  rw [hM]
  rcases le_total (b+1) (c+e) with hxy|hyx
  · have hp := product_lower f (unitCost b c 1 e-f) (c+e+1) (by omega) (by omega)
    have hT : 2*(c+e)+2≤b*c+c+e := by rw [←hcost]; omega
    have hbound := d_one_ordered_y b c e hb2 hc2 (by omega) hxy hT
    have hprod : (c+e+1)*(b*c+1)≤f*(unitCost b c 1 e-f+2) := by
      nlinarith [hp,hcost]
    omega
  · have hp := product_lower f (unitCost b c 1 e-f) (b+2) (by omega) (by omega)
    have hbound := d_one_ordered_x b c e hb2 hc2 (by omega) hyx
    have hprod : (b+2)*(b*c+c+e-b)≤f*(unitCost b c 1 e-f+2) := by
      nlinarith [hp,hcost]
    omega

theorem unitMarkov_swap_pairs (b c d e f : Int) :
    unitMarkov b c d e f=unitMarkov e d c b f := by
  unfold unitMarkov unitCost
  ring

theorem unitPfaffian_swap_pairs (b c d e f : Int) :
    unitPfaffian b c d e f=unitPfaffian e d c b f := by
  unfold unitPfaffian
  ring

theorem c_one_overflow_pfaffian (b d e f : Int) (H : Nat)
    (hb : 0<b) (hd : 0<d) (he : 0<e)
    (hbd : b+d≤(H:Int)) (hce : 1+e≤(H:Int))
    (hf : (H:Int)<f) (hover : f+(H:Int)<unitCost b 1 d e) :
    0<unitPfaffian b 1 d e f ∧
      unitMarkov b 1 d e f-2*unitPfaffian b 1 d e f≤-5 := by
  have hover' : f+(H:Int)<unitCost e d 1 b := by
    simpa [unitCost,mul_comm,add_comm,add_left_comm,add_assoc] using hover
  have h := d_one_overflow_pfaffian e d b f H he hd hb (by omega) (by omega) hf hover'
  rw [unitMarkov_swap_pairs b 1 d e f,unitPfaffian_swap_pairs b 1 d e f]
  exact h

/-- The scalar comparison supplies the missing unit-incident guard. Its
connection to semantic MA is a separate explicit structural obligation. -/
theorem unit_incident_one_guard (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hcd : c=1 ∨ d=1)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hm : 2*unitPfaffian b c d e f≤unitMarkov b c d e f) :
    PrefixHeightLe (mutate (unitPeak b c d e f) 0) [1,0,1] H := by
  have hec := h0 1 3
  have hbd := h1 0 2
  unfold unitPeak at hec hbd
  rw [positivePeak_zero 1 b c d e f (by decide) hb hc] at hec
  rw [positivePeak_one 1 b c d e f (by decide) hd he] at hbd
  simp only [ofSix] at hec hbd
  apply (unitPeak_detour_iff b c d e f H hb hc hd he h0 h1).mpr
  by_contra hguard
  have hover : f+(H:Int)<unitCost b c d e := by omega
  rcases hcd with rfl|rfl
  · have h := (c_one_overflow_pfaffian b d e f H hb hd he
      (by omega) (by omega) hf hover).2
    omega
  · have h := (d_one_overflow_pfaffian b c e f H hb hc he
      (by omega) (by omega) hf hover).2
    omega

theorem unit_incident_one_count_decrease (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e) (hcd : c=1 ∨ d=1)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hm : 2*unitPfaffian b c d e f≤unitMarkov b c d e f)
    (tail : List (Fin 4)) :
    overCount (mutate (unitPeak b c d e f) 0)
        ([1,0,1]++tail.map Forks.swap01.invFun) H + 1 =
      overCount (mutate (unitPeak b c d e f) 0) ([0,1]++tail) H := by
  apply strict_peak_overCount _ 0 1 [1,0,1] tail Forks.swap01 H _ h1
    (unitPeak_detour_endpoint b c d e f hb hc hd he)
    (unit_incident_one_guard b c d e f H hb hc hd he hcd h0 h1 hf hm)
  intro hP
  have h := (hP 2 3).2
  simp only [unitPeak,positivePeak,ofSix] at h
  omega

#print axioms d_one_overflow_pfaffian
#print axioms c_one_overflow_pfaffian
#print axioms unit_incident_one_guard
#print axioms unit_incident_one_count_decrease
end Rank4Round2
