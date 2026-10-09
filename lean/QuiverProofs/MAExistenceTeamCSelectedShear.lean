import QuiverProofs.MAExistenceTeamBOrderMutation

/-! Exact selected proper mutation in the actual vertex labels.

The source linear representative is retained in the bilinear identity. Cyclic
rotations are used only as witnesses of the proper-mutation cut. Twenty local
arbitrary-integer sign cases cover both pivot colors and all pivot positions;
finite permutation computations only reindex the four-term matrix products.
No coefficient sign coherence, companion admissibility, all-word preservation,
or total properness is assumed or concluded here. Absent edges, cancellation,
singular matrices, and disconnected supports are included.
-/
namespace QuiverProofs.MAExistenceTeamCSelectedShear
open ProperOrder ProperWiggle ProperMutation MAExistenceLiterature
open MAExistenceCompanions MAExistenceTeamBOrderMutation Cosquare MutationCongruence Census
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem inv_0_0 : (permutation 0).invFun 0 = 0 := by decide
private theorem inv_0_1 : (permutation 0).invFun 1 = 1 := by decide
private theorem inv_0_2 : (permutation 0).invFun 2 = 2 := by decide
private theorem inv_0_3 : (permutation 0).invFun 3 = 3 := by decide
private theorem inv_1_0 : (permutation 1).invFun 0 = 0 := by decide
private theorem inv_1_1 : (permutation 1).invFun 1 = 1 := by decide
private theorem inv_1_2 : (permutation 1).invFun 2 = 3 := by decide
private theorem inv_1_3 : (permutation 1).invFun 3 = 2 := by decide
private theorem inv_2_0 : (permutation 2).invFun 0 = 0 := by decide
private theorem inv_2_1 : (permutation 2).invFun 1 = 2 := by decide
private theorem inv_2_2 : (permutation 2).invFun 2 = 1 := by decide
private theorem inv_2_3 : (permutation 2).invFun 3 = 3 := by decide
private theorem inv_3_0 : (permutation 3).invFun 0 = 0 := by decide
private theorem inv_3_1 : (permutation 3).invFun 1 = 3 := by decide
private theorem inv_3_2 : (permutation 3).invFun 2 = 1 := by decide
private theorem inv_3_3 : (permutation 3).invFun 3 = 2 := by decide
private theorem inv_4_0 : (permutation 4).invFun 0 = 0 := by decide
private theorem inv_4_1 : (permutation 4).invFun 1 = 2 := by decide
private theorem inv_4_2 : (permutation 4).invFun 2 = 3 := by decide
private theorem inv_4_3 : (permutation 4).invFun 3 = 1 := by decide
private theorem inv_6_0 : (permutation 6).invFun 0 = 1 := by decide
private theorem inv_6_1 : (permutation 6).invFun 1 = 0 := by decide
private theorem inv_6_2 : (permutation 6).invFun 2 = 2 := by decide
private theorem inv_6_3 : (permutation 6).invFun 3 = 3 := by decide
private theorem inv_8_0 : (permutation 8).invFun 0 = 2 := by decide
private theorem inv_8_1 : (permutation 8).invFun 1 = 0 := by decide
private theorem inv_8_2 : (permutation 8).invFun 2 = 1 := by decide
private theorem inv_8_3 : (permutation 8).invFun 3 = 3 := by decide
private theorem inv_9_0 : (permutation 9).invFun 0 = 3 := by decide
private theorem inv_9_1 : (permutation 9).invFun 1 = 0 := by decide
private theorem inv_9_2 : (permutation 9).invFun 2 = 1 := by decide
private theorem inv_9_3 : (permutation 9).invFun 3 = 2 := by decide
private theorem inv_12_0 : (permutation 12).invFun 0 = 1 := by decide
private theorem inv_12_1 : (permutation 12).invFun 1 = 2 := by decide
private theorem inv_12_2 : (permutation 12).invFun 2 = 0 := by decide
private theorem inv_12_3 : (permutation 12).invFun 3 = 3 := by decide
private theorem inv_18_0 : (permutation 18).invFun 0 = 1 := by decide
private theorem inv_18_1 : (permutation 18).invFun 1 = 2 := by decide
private theorem inv_18_2 : (permutation 18).invFun 2 = 3 := by decide
private theorem inv_18_3 : (permutation 18).invFun 3 = 0 := by decide

private theorem eq_g00 (a b c d e f : Int) (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0) :
    labeledUnipotent (mutate (ofSix a b c d e f) 0) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0) := by
  have hm_a : max a 0 = 0 := by omega
  have hm_na : max (-a) 0 = -a := by omega
  have hm_b : max b 0 = 0 := by omega
  have hm_nb : max (-b) 0 = -b := by omega
  have hm_c : max c 0 = 0 := by omega
  have hm_nc : max (-c) 0 = -c := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_b, hm_nb, hm_c, hm_nc,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g01 (a b c d e f : Int) (ha : 0 ≤ a) (hb : b ≤ 0) (hc : c ≤ 0) :
    labeledUnipotent (mutate (ofSix a b c d e f) 0) (permutation 6) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_b : max b 0 = 0 := by omega
  have hm_nb : max (-b) 0 = -b := by omega
  have hm_c : max c 0 = 0 := by omega
  have hm_nc : max (-c) 0 = -c := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_6_0, inv_6_1, inv_6_2, inv_6_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_b, hm_nb, hm_c, hm_nc,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g02 (a b c d e f : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 0) :
    labeledUnipotent (mutate (ofSix a b c d e f) 0) (permutation 8) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_b : max b 0 = b := by omega
  have hm_nb : max (-b) 0 = 0 := by omega
  have hm_c : max c 0 = 0 := by omega
  have hm_nc : max (-c) 0 = -c := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_8_0, inv_8_1, inv_8_2, inv_8_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_b, hm_nb, hm_c, hm_nc,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g03 (a b c d e f : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    labeledUnipotent (mutate (ofSix a b c d e f) 0) (permutation 9) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 0) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_b : max b 0 = b := by omega
  have hm_nb : max (-b) 0 = 0 := by omega
  have hm_c : max c 0 = c := by omega
  have hm_nc : max (-c) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_9_0, inv_9_1, inv_9_2, inv_9_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_b, hm_nb, hm_c, hm_nc,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g10 (a b c d e f : Int) (ha : 0 ≤ a) (hd : d ≤ 0) (he : e ≤ 0) :
    labeledUnipotent (mutate (ofSix a b c d e f) 1) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 1))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 1) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_d : max d 0 = 0 := by omega
  have hm_nd : max (-d) 0 = -d := by omega
  have hm_e : max e 0 = 0 := by omega
  have hm_ne : max (-e) 0 = -e := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_d, hm_nd, hm_e, hm_ne,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g11 (a b c d e f : Int) (ha : 0 ≤ a) (hd : 0 ≤ d) (he : e ≤ 0) :
    labeledUnipotent (mutate (ofSix a b c d e f) 1) (permutation 2) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 1))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 1) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_e : max e 0 = 0 := by omega
  have hm_ne : max (-e) 0 = -e := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_2_0, inv_2_1, inv_2_2, inv_2_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_d, hm_nd, hm_e, hm_ne,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g12 (a b c d e f : Int) (ha : 0 ≤ a) (hd : 0 ≤ d) (he : 0 ≤ e) :
    labeledUnipotent (mutate (ofSix a b c d e f) 1) (permutation 3) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 1))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 1) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_e : max e 0 = e := by omega
  have hm_ne : max (-e) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_3_0, inv_3_1, inv_3_2, inv_3_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_d, hm_nd, hm_e, hm_ne,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g20 (a b c d e f : Int) (hb : 0 ≤ b) (hd : 0 ≤ d) (hf : f ≤ 0) :
    labeledUnipotent (mutate (ofSix a b c d e f) 2) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 2))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 2) := by
  have hm_b : max b 0 = b := by omega
  have hm_nb : max (-b) 0 = 0 := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_f : max f 0 = 0 := by omega
  have hm_nf : max (-f) 0 = -f := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_b, hm_nb, hm_d, hm_nd, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g21 (a b c d e f : Int) (hb : 0 ≤ b) (hd : 0 ≤ d) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 2) (permutation 1) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 2))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 2) := by
  have hm_b : max b 0 = b := by omega
  have hm_nb : max (-b) 0 = 0 := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_1_0, inv_1_1, inv_1_2, inv_1_3,
      mutate, correction, ofSix, mul, hm_b, hm_nb, hm_d, hm_nd, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_g30 (a b c d e f : Int) (hc : 0 ≤ c) (he : 0 ≤ e) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 3) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => true) 3))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => true) 3) := by
  have hm_c : max c 0 = c := by omega
  have hm_nc : max (-c) 0 = 0 := by omega
  have hm_e : max e 0 = e := by omega
  have hm_ne : max (-e) 0 = 0 := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_c, hm_nc, hm_e, hm_ne, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r00 (a b c d e f : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    labeledUnipotent (mutate (ofSix a b c d e f) 0) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 0))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 0) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_b : max b 0 = b := by omega
  have hm_nb : max (-b) 0 = 0 := by omega
  have hm_c : max c 0 = c := by omega
  have hm_nc : max (-c) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_b, hm_nb, hm_c, hm_nc,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r10 (a b c d e f : Int) (ha : a ≤ 0) (hd : 0 ≤ d) (he : 0 ≤ e) :
    labeledUnipotent (mutate (ofSix a b c d e f) 1) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 1))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 1) := by
  have hm_a : max a 0 = 0 := by omega
  have hm_na : max (-a) 0 = -a := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_e : max e 0 = e := by omega
  have hm_ne : max (-e) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_d, hm_nd, hm_e, hm_ne,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r11 (a b c d e f : Int) (ha : 0 ≤ a) (hd : 0 ≤ d) (he : 0 ≤ e) :
    labeledUnipotent (mutate (ofSix a b c d e f) 1) (permutation 6) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 1))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 1) := by
  have hm_a : max a 0 = a := by omega
  have hm_na : max (-a) 0 = 0 := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_e : max e 0 = e := by omega
  have hm_ne : max (-e) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_6_0, inv_6_1, inv_6_2, inv_6_3,
      mutate, correction, ofSix, mul, hm_a, hm_na, hm_d, hm_nd, hm_e, hm_ne,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r20 (a b c d e f : Int) (hb : b ≤ 0) (hd : d ≤ 0) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 2) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 2))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 2) := by
  have hm_b : max b 0 = 0 := by omega
  have hm_nb : max (-b) 0 = -b := by omega
  have hm_d : max d 0 = 0 := by omega
  have hm_nd : max (-d) 0 = -d := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_b, hm_nb, hm_d, hm_nd, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r21 (a b c d e f : Int) (hb : b ≤ 0) (hd : 0 ≤ d) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 2) (permutation 2) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 2))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 2) := by
  have hm_b : max b 0 = 0 := by omega
  have hm_nb : max (-b) 0 = -b := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_2_0, inv_2_1, inv_2_2, inv_2_3,
      mutate, correction, ofSix, mul, hm_b, hm_nb, hm_d, hm_nd, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r22 (a b c d e f : Int) (hb : 0 ≤ b) (hd : 0 ≤ d) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 2) (permutation 12) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 2))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 2) := by
  have hm_b : max b 0 = b := by omega
  have hm_nb : max (-b) 0 = 0 := by omega
  have hm_d : max d 0 = d := by omega
  have hm_nd : max (-d) 0 = 0 := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_12_0, inv_12_1, inv_12_2, inv_12_3,
      mutate, correction, ofSix, mul, hm_b, hm_nb, hm_d, hm_nd, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r30 (a b c d e f : Int) (hc : c ≤ 0) (he : e ≤ 0) (hf : f ≤ 0) :
    labeledUnipotent (mutate (ofSix a b c d e f) 3) (permutation 0) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3) := by
  have hm_c : max c 0 = 0 := by omega
  have hm_nc : max (-c) 0 = -c := by omega
  have hm_e : max e 0 = 0 := by omega
  have hm_ne : max (-e) 0 = -e := by omega
  have hm_f : max f 0 = 0 := by omega
  have hm_nf : max (-f) 0 = -f := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      mutate, correction, ofSix, mul, hm_c, hm_nc, hm_e, hm_ne, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r31 (a b c d e f : Int) (hc : c ≤ 0) (he : e ≤ 0) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 3) (permutation 1) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3) := by
  have hm_c : max c 0 = 0 := by omega
  have hm_nc : max (-c) 0 = -c := by omega
  have hm_e : max e 0 = 0 := by omega
  have hm_ne : max (-e) 0 = -e := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_1_0, inv_1_1, inv_1_2, inv_1_3,
      mutate, correction, ofSix, mul, hm_c, hm_nc, hm_e, hm_ne, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r32 (a b c d e f : Int) (hc : c ≤ 0) (he : 0 ≤ e) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 3) (permutation 4) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3) := by
  have hm_c : max c 0 = 0 := by omega
  have hm_nc : max (-c) 0 = -c := by omega
  have hm_e : max e 0 = e := by omega
  have hm_ne : max (-e) 0 = 0 := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_4_0, inv_4_1, inv_4_2, inv_4_3,
      mutate, correction, ofSix, mul, hm_c, hm_nc, hm_e, hm_ne, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

private theorem eq_r33 (a b c d e f : Int) (hc : 0 ≤ c) (he : 0 ≤ e) (hf : 0 ≤ f) :
    labeledUnipotent (mutate (ofSix a b c d e f) 3) (permutation 18) =
      mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3))
        (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
        (coefficientBasis (ofSix a b c d e f) (fun _ => false) 3) := by
  have hm_c : max c 0 = c := by omega
  have hm_nc : max (-c) 0 = 0 := by omega
  have hm_e : max e 0 = e := by omega
  have hm_ne : max (-e) 0 = 0 := by omega
  have hm_f : max f 0 = f := by omega
  have hm_nf : max (-f) 0 = 0 := by omega
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [labeledUnipotent, inv_0_0, inv_0_1, inv_0_2, inv_0_3,
      inv_18_0, inv_18_1, inv_18_2, inv_18_3,
      mutate, correction, ofSix, mul, hm_c, hm_nc, hm_e, hm_ne, hm_f, hm_nf,
      transpose, coefficientBasis, pivotWeight] <;> grind

/-- In the original linear identity frame, select a cut output realizing the
prescribed green/red shear exactly. Properness and pivot-side data are explicit. -/
theorem selected_shear_six (a b c d e f : Int) (g : Bool) (k : Fin 4)
    (hp : ProperVertex (ofSix a b c d e f) (permutation 0) k)
    (hg : g = true → ∀ j, 0 < ofSix a b c d e f k j → k < j)
    (hr : g = false → ∀ j, 0 < ofSix a b c d e f j k → j < k) :
    ∃ q : CyclicOrder, ProperMutation (ofSix a b c d e f) (permutation 0) k q ∧
      labeledUnipotent (mutate (ofSix a b c d e f) k) q =
        mul (mul (transpose (coefficientBasis (ofSix a b c d e f) (fun _ => g) k))
          (labeledUnipotent (ofSix a b c d e f) (permutation 0)))
          (coefficientBasis (ofSix a b c d e f) (fun _ => g) k) := by
  cases g <;> rcases fin4 k with rfl|rfl|rfl|rfl
  · have hs := hr rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    have ha : 0 ≤ a := by omega
    have hb : 0 ≤ b := by omega
    have hc : 0 ≤ c := by omega
    refine ⟨permutation 0, ?_, eq_r00 a b c d e f ha hb hc⟩
    refine ⟨permutation 0, 3, .same (by decide), by decide, ?_, .same (by decide)⟩
    change 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c
    omega
  · have hs := hr rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    by_cases hapos : 0 < a
    ·
      have ha : 0 ≤ a := by omega
      have hd : 0 ≤ d := by omega
      have he : 0 ≤ e := by omega
      refine ⟨permutation 6, ?_, eq_r11 a b c d e f ha hd he⟩
      refine ⟨permutation 9, 2, .same (by decide), by decide, ?_, .same (by decide)⟩
      change 0 ≤ d ∧ 0 ≤ e ∧ -a ≤ 0
      omega
    ·
      have ha : a ≤ 0 := by omega
      have hd : 0 ≤ d := by omega
      have he : 0 ≤ e := by omega
      refine ⟨permutation 0, ?_, eq_r10 a b c d e f ha hd he⟩
      refine ⟨permutation 9, 3, .same (by decide), by decide, ?_, .same (by decide)⟩
      change 0 ≤ d ∧ 0 ≤ e ∧ 0 ≤ -a
      omega
  · have hs := hr rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    by_cases hbpos : 0 < b
    ·
      have hb : 0 ≤ b := by omega
      have hd : 0 ≤ d := by omega
      have hf : 0 ≤ f := by omega
      refine ⟨permutation 12, ?_, eq_r22 a b c d e f hb hd hf⟩
      refine ⟨permutation 16, 1, .same (by decide), by decide, ?_, .same (by decide)⟩
      change 0 ≤ f ∧ -b ≤ 0 ∧ -d ≤ 0
      omega
    ·
      by_cases hdpos : 0 < d
      ·
        have hb : b ≤ 0 := by omega
        have hd : 0 ≤ d := by omega
        have hf : 0 ≤ f := by omega
        refine ⟨permutation 2, ?_, eq_r21 a b c d e f hb hd hf⟩
        refine ⟨permutation 16, 2, .same (by decide), by decide, ?_, .same (by decide)⟩
        change 0 ≤ f ∧ 0 ≤ -b ∧ -d ≤ 0
        omega
      ·
        have hb : b ≤ 0 := by omega
        have hd : d ≤ 0 := by omega
        have hf : 0 ≤ f := by omega
        refine ⟨permutation 0, ?_, eq_r20 a b c d e f hb hd hf⟩
        refine ⟨permutation 16, 3, .same (by decide), by decide, ?_, .same (by decide)⟩
        change 0 ≤ f ∧ 0 ≤ -b ∧ 0 ≤ -d
        omega
  · have hs := hr rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    by_cases hcpos : 0 < c
    ·
      have hc : 0 ≤ c := by omega
      have he : 0 ≤ e := by omega
      have hf : 0 ≤ f := by omega
      refine ⟨permutation 18, ?_, eq_r33 a b c d e f hc he hf⟩
      refine ⟨permutation 18, 0, .same (by decide), by decide, ?_, .same (by decide)⟩
      change -c ≤ 0 ∧ -e ≤ 0 ∧ -f ≤ 0
      omega
    ·
      by_cases hepos : 0 < e
      ·
        have hc : c ≤ 0 := by omega
        have he : 0 ≤ e := by omega
        have hf : 0 ≤ f := by omega
        refine ⟨permutation 4, ?_, eq_r32 a b c d e f hc he hf⟩
        refine ⟨permutation 18, 1, .same (by decide), by decide, ?_, .same (by decide)⟩
        change 0 ≤ -c ∧ -e ≤ 0 ∧ -f ≤ 0
        omega
      ·
        by_cases hfpos : 0 < f
        ·
          have hc : c ≤ 0 := by omega
          have he : e ≤ 0 := by omega
          have hf : 0 ≤ f := by omega
          refine ⟨permutation 1, ?_, eq_r31 a b c d e f hc he hf⟩
          refine ⟨permutation 18, 2, .same (by decide), by decide, ?_, .same (by decide)⟩
          change 0 ≤ -c ∧ 0 ≤ -e ∧ -f ≤ 0
          omega
        ·
          have hc : c ≤ 0 := by omega
          have he : e ≤ 0 := by omega
          have hf : f ≤ 0 := by omega
          refine ⟨permutation 0, ?_, eq_r30 a b c d e f hc he hf⟩
          refine ⟨permutation 18, 3, .same (by decide), by decide, ?_, .same (by decide)⟩
          change 0 ≤ -c ∧ 0 ≤ -e ∧ 0 ≤ -f
          omega
  · have hs := hg rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    by_cases hcpos : 0 < c
    ·
      have ha : 0 ≤ a := by omega
      have hb : 0 ≤ b := by omega
      have hc : 0 ≤ c := by omega
      refine ⟨permutation 9, ?_, eq_g03 a b c d e f ha hb hc⟩
      refine ⟨permutation 0, 3, .same (by decide), by decide, ?_, .same (by decide)⟩
      change 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c
      omega
    ·
      by_cases hbpos : 0 < b
      ·
        have ha : 0 ≤ a := by omega
        have hb : 0 ≤ b := by omega
        have hc : c ≤ 0 := by omega
        refine ⟨permutation 8, ?_, eq_g02 a b c d e f ha hb hc⟩
        refine ⟨permutation 0, 2, .same (by decide), by decide, ?_, .same (by decide)⟩
        change 0 ≤ a ∧ 0 ≤ b ∧ c ≤ 0
        omega
      ·
        by_cases hapos : 0 < a
        ·
          have ha : 0 ≤ a := by omega
          have hb : b ≤ 0 := by omega
          have hc : c ≤ 0 := by omega
          refine ⟨permutation 6, ?_, eq_g01 a b c d e f ha hb hc⟩
          refine ⟨permutation 0, 1, .same (by decide), by decide, ?_, .same (by decide)⟩
          change 0 ≤ a ∧ b ≤ 0 ∧ c ≤ 0
          omega
        ·
          have ha : a ≤ 0 := by omega
          have hb : b ≤ 0 := by omega
          have hc : c ≤ 0 := by omega
          refine ⟨permutation 0, ?_, eq_g00 a b c d e f ha hb hc⟩
          refine ⟨permutation 0, 0, .same (by decide), by decide, ?_, .same (by decide)⟩
          change a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0
          omega
  · have hs := hg rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    by_cases hepos : 0 < e
    ·
      have ha : 0 ≤ a := by omega
      have hd : 0 ≤ d := by omega
      have he : 0 ≤ e := by omega
      refine ⟨permutation 3, ?_, eq_g12 a b c d e f ha hd he⟩
      refine ⟨permutation 9, 2, .same (by decide), by decide, ?_, .same (by decide)⟩
      change 0 ≤ d ∧ 0 ≤ e ∧ -a ≤ 0
      omega
    ·
      by_cases hdpos : 0 < d
      ·
        have ha : 0 ≤ a := by omega
        have hd : 0 ≤ d := by omega
        have he : e ≤ 0 := by omega
        refine ⟨permutation 2, ?_, eq_g11 a b c d e f ha hd he⟩
        refine ⟨permutation 9, 1, .same (by decide), by decide, ?_, .same (by decide)⟩
        change 0 ≤ d ∧ e ≤ 0 ∧ -a ≤ 0
        omega
      ·
        have ha : 0 ≤ a := by omega
        have hd : d ≤ 0 := by omega
        have he : e ≤ 0 := by omega
        refine ⟨permutation 0, ?_, eq_g10 a b c d e f ha hd he⟩
        refine ⟨permutation 9, 0, .same (by decide), by decide, ?_, .same (by decide)⟩
        change d ≤ 0 ∧ e ≤ 0 ∧ -a ≤ 0
        omega
  · have hs := hg rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    by_cases hfpos : 0 < f
    ·
      have hb : 0 ≤ b := by omega
      have hd : 0 ≤ d := by omega
      have hf : 0 ≤ f := by omega
      refine ⟨permutation 1, ?_, eq_g21 a b c d e f hb hd hf⟩
      refine ⟨permutation 16, 1, .same (by decide), by decide, ?_, .same (by decide)⟩
      change 0 ≤ f ∧ -b ≤ 0 ∧ -d ≤ 0
      omega
    ·
      have hb : 0 ≤ b := by omega
      have hd : 0 ≤ d := by omega
      have hf : f ≤ 0 := by omega
      refine ⟨permutation 0, ?_, eq_g20 a b c d e f hb hd hf⟩
      refine ⟨permutation 16, 0, .same (by decide), by decide, ?_, .same (by decide)⟩
      change f ≤ 0 ∧ -b ≤ 0 ∧ -d ≤ 0
      omega
  · have hs := hg rfl
    have hs0 := hs 0
    have hs1 := hs 1
    have hs2 := hs 2
    have hs3 := hs 3
    have hp01 := hp 0 1
    have hp02 := hp 0 2
    have hp03 := hp 0 3
    have hp10 := hp 1 0
    have hp12 := hp 1 2
    have hp13 := hp 1 3
    have hp20 := hp 2 0
    have hp21 := hp 2 1
    have hp23 := hp 2 3
    have hp30 := hp 3 0
    have hp31 := hp 3 1
    have hp32 := hp 3 2
    simp [Between, Clockwise, ofSix, inv_0_0, inv_0_1, inv_0_2, inv_0_3] at hs0 hs1 hs2 hs3 hp01 hp02 hp03 hp10 hp12 hp13 hp20 hp21 hp23 hp30 hp31 hp32
    have hc : 0 ≤ c := by omega
    have he : 0 ≤ e := by omega
    have hf : 0 ≤ f := by omega
    refine ⟨permutation 0, ?_, eq_g30 a b c d e f hc he hf⟩
    refine ⟨permutation 18, 0, .same (by decide), by decide, ?_, .same (by decide)⟩
    change -c ≤ 0 ∧ -e ≤ 0 ∧ -f ≤ 0
    omega

private theorem relabeling_ext (p q : CyclicOrder) (h : p.toFun = q.toFun) : p = q := by
  have hi : p.invFun = q.invFun := by
    funext i
    apply p.injective
    rw [p.right_inv, h, q.right_inv]
  cases p
  cases q
  simp_all

private theorem identity_permutation : permutation 0 = Relabeling.identity 4 := by
  apply relabeling_ext
  funext i
  exact (show ∀ i : Fin 4, (permutation 0).toFun i = i by decide) i

private theorem four_sum_permutation (p : Fin 24) (f : Fin 4 → Int) :
    f ((permutation p).toFun 0) + f ((permutation p).toFun 1) +
      f ((permutation p).toFun 2) + f ((permutation p).toFun 3) =
      f 0 + f 1 + f 2 + f 3 := by
  have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 ∨ p = 21 ∨ p = 22 ∨ p = 23 := by omega
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change f 0 + f 1 + f 2 + f 3 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 0 + f 1 + f 3 + f 2 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 0 + f 2 + f 1 + f 3 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 0 + f 2 + f 3 + f 1 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 0 + f 3 + f 1 + f 2 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 0 + f 3 + f 2 + f 1 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 1 + f 0 + f 2 + f 3 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 1 + f 0 + f 3 + f 2 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 1 + f 2 + f 0 + f 3 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 1 + f 2 + f 3 + f 0 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 1 + f 3 + f 0 + f 2 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 1 + f 3 + f 2 + f 0 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 2 + f 0 + f 1 + f 3 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 2 + f 0 + f 3 + f 1 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 2 + f 1 + f 0 + f 3 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 2 + f 1 + f 3 + f 0 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 2 + f 3 + f 0 + f 1 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 2 + f 3 + f 1 + f 0 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 3 + f 0 + f 1 + f 2 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 3 + f 0 + f 2 + f 1 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 3 + f 1 + f 0 + f 2 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 3 + f 1 + f 2 + f 0 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 3 + f 2 + f 0 + f 1 = f 0 + f 1 + f 2 + f 3
    omega
  · change f 3 + f 2 + f 1 + f 0 = f 0 + f 1 + f 2 + f 3
    omega

private theorem four_sum_relabel (p : CyclicOrder) (f : Fin 4 → Int) :
    f (p.toFun 0) + f (p.toFun 1) + f (p.toFun 2) + f (p.toFun 3) =
      f 0 + f 1 + f 2 + f 3 := by
  obtain ⟨i, hi⟩ := permutation_exhaustive p
  rw [hi]
  exact four_sum_permutation i f

private theorem relabel_mul (A B : Matrix 4) (p : CyclicOrder) :
    relabel (mul A B) p = mul (relabel A p) (relabel B p) := by
  funext i j
  exact (four_sum_relabel p (fun k => A (p.toFun i) k * B k (p.toFun j))).symm

private theorem relabel_transpose (A : Matrix 4) (p : CyclicOrder) :
    relabel (transpose A) p = transpose (relabel A p) := rfl

private theorem relabel_injective (A B : Matrix 4) (p : CyclicOrder)
    (h : relabel A p = relabel B p) : A = B := by
  funext i j
  have hh := congrFun (congrFun h (p.invFun i)) (p.invFun j)
  simpa only [relabel, p.right_inv] using hh

private theorem relabel_labeledUnipotent (B : Matrix 4) (p q : CyclicOrder) :
    relabel (labeledUnipotent B (p.trans q)) p =
      labeledUnipotent (relabel B p) q := by
  funext i j
  have he : p.toFun i = p.toFun j ↔ i = j :=
    ⟨p.injective, fun h => congrArg p.toFun h⟩
  simp only [relabel, labeledUnipotent, Relabeling.trans, Function.comp_apply,
    p.left_inv, he]

private theorem relabel_coefficientBasis (B : Matrix 4) (green : Colors)
    (k : Fin 4) (p : CyclicOrder) :
    relabel (coefficientBasis B green k) p =
      coefficientBasis (relabel B p) (fun i => green (p.toFun i)) (p.invFun k) := by
  funext i j
  have hik : p.toFun i = k ↔ i = p.invFun k := by
    constructor
    · intro h
      simpa only [p.left_inv] using congrArg p.invFun h
    · intro h
      rw [h, p.right_inv]
  have hjk : p.toFun j = k ↔ j = p.invFun k := by
    constructor
    · intro h
      simpa only [p.left_inv] using congrArg p.invFun h
    · intro h
      rw [h, p.right_inv]
  have hij : p.toFun i = p.toFun j ↔ i = j :=
    ⟨p.injective, fun h => congrArg p.toFun h⟩
  simp only [relabel, coefficientBasis, pivotWeight, hik, hjk, hij, p.right_inv]

private theorem same_left_relabel (p r s : CyclicOrder)
    (h : SameCyclicOrder r s) : SameCyclicOrder (p.trans r) (p.trans s) := by
  intro i j k
  exact h (p.invFun i) (p.invFun j) (p.invFun k)

private theorem wiggle_left_relabel (B : Matrix 4) (p r s : CyclicOrder)
    (h : WiggleEquivalent (relabel B p) r s) :
    WiggleEquivalent B (p.trans r) (p.trans s) := by
  induction h with
  | same h => exact .same (same_left_relabel p _ _ h)
  | step h =>
    obtain ⟨t, a, hrt, hz, hts⟩ := h
    exact .step ⟨p.trans t, a, same_left_relabel p _ _ hrt, hz,
      same_left_relabel p _ _ hts⟩
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

private theorem properMutation_left_relabel (B : Matrix 4) (p r s : CyclicOrder)
    (k : Fin 4) (h : ProperMutation (relabel B p) r k s) :
    ProperMutation B (p.trans r) (p.toFun k) (p.trans s) := by
  obtain ⟨t, c, hrt, hk, hc, hts⟩ := h
  refine ⟨p.trans t, c, wiggle_left_relabel B p _ _ hrt, ?_, hc, ?_⟩
  · exact congrArg p.toFun hk
  · rw [mutate_relabel] at hts
    exact wiggle_left_relabel (mutate B (p.toFun k)) p _ _ hts


/-- Select an actual proper-mutation output realizing exactly the prescribed
coefficient shear, without changing the source's linear representative. -/
theorem selected_shear (B : Matrix 4) (hB : SkewSymmetric B)
    (green : Colors) (p : CyclicOrder) (k : Fin 4)
    (hp : ProperVertex B p k)
    (hg : green k = true → ∀ j, 0 < B k j → p.invFun k < p.invFun j)
    (hr : green k = false → ∀ j, 0 < B j k → p.invFun j < p.invFun k) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧
      labeledUnipotent (mutate B k) q =
        mul (mul (transpose (coefficientBasis B green k)) (labeledUnipotent B p))
          (coefficientBasis B green k) := by
  let D := relabel B p
  let kp := p.invFun k
  have hD : SkewSymmetric D := relabel_skew B p hB
  have hpD : ProperVertex D (permutation 0) kp := by
    intro u w huk hkw
    have hu : 0 < B (p.toFun u) k := by
      simpa only [D, kp, relabel, p.right_inv] using huk
    have hw : 0 < B k (p.toFun w) := by
      simpa only [D, kp, relabel, p.right_inv] using hkw
    have hh := hp (p.toFun u) (p.toFun w) hu hw
    simpa only [Between, identity_permutation, Relabeling.identity, id_eq,
      p.left_inv] using hh
  have hgD : green k = true → ∀ j, 0 < D kp j → kp < j := by
    intro hk j hj
    have hbj : 0 < B k (p.toFun j) := by
      simpa only [D, kp, relabel, p.right_inv] using hj
    simpa only [kp, p.left_inv] using hg hk (p.toFun j) hbj
  have hrD : green k = false → ∀ j, 0 < D j kp → j < kp := by
    intro hk j hj
    have hbj : 0 < B (p.toFun j) k := by
      simpa only [D, kp, relabel, p.right_inv] using hj
    simpa only [kp, p.left_inv] using hr hk (p.toFun j) hbj
  have hrec := ofSix_reconstruct D hD
  have hframe := selected_shear_six (D 0 1) (D 0 2) (D 0 3)
    (D 1 2) (D 1 3) (D 2 3) (green k) kp
  rw [hrec] at hframe
  obtain ⟨q, hmq, heq⟩ := hframe hpD hgD hrD
  refine ⟨p.trans q, ?_, ?_⟩
  · have hm := properMutation_left_relabel B p (permutation 0) q kp hmq
    simpa only [identity_permutation, Relabeling.trans, Relabeling.identity,
      Function.comp_id, kp, p.right_inv] using hm
  · apply relabel_injective _ _ p
    have hsource : relabel (labeledUnipotent B p) p =
        labeledUnipotent D (permutation 0) := by
      rw [identity_permutation]
      exact relabel_labeledUnipotent B p (Relabeling.identity 4)
    have hE : relabel (coefficientBasis B green k) p =
        coefficientBasis D (fun _ => green k) kp := by
      rw [relabel_coefficientBasis]
      funext i j
      simp only [coefficientBasis, pivotWeight, D, kp, p.right_inv]
    rw [relabel_labeledUnipotent, relabel_mul, relabel_mul,
      relabel_transpose, hE, hsource]
    have hex : relabel (mutate B k) p = mutate D kp := by
      have h := mutate_relabel B p kp
      simpa only [D, kp, p.right_inv] using h.symm
    rw [hex]
    exact heq

/-- Current auxiliary compatibility and the color block give precisely the
pivot-side data needed by the selected shear construction. -/
theorem compatible_selected_shear (B : Matrix 4) (hB : SkewSymmetric B)
    (green : Colors) (p : CyclicOrder) (k : Fin 4)
    (hp : Compatible B green k p) (hc : GreenBeforeRed green p) :
    ∃ q : CyclicOrder, ProperMutation B p k q ∧
      labeledUnipotent (mutate B k) q =
        mul (mul (transpose (coefficientBasis B green k)) (labeledUnipotent B p))
          (coefficientBasis B green k) := by
  apply selected_shear B hB green p k (compatible_colorBlock_proper B green k p hp hc)
  · intro hk j hkj
    cases hj : green j
    · exact hc k j hk hj
    · exact hp k j (Or.inl ⟨hkj, by simp [hk, hj]⟩)
  · intro hk j hjk
    cases hj : green j
    · exact hp j k (Or.inl ⟨hjk, by simp [hk, hj]⟩)
    · exact hc j k hj hk

end QuiverProofs.MAExistenceTeamCSelectedShear
