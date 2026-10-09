import Rank4CoordinatorR2.FlatHalfShape
import Rank4Round2.SignedTransport

/-! A flat step at an endpoint of the unique top opposite edge must use a
unit edge to the entering pivot. This follows from integer bounds alone,
without any triangle-heredity or MA premise. -/
namespace Rank4CoordinatorR2.FlatSwitch
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2

theorem entry_paths (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hf : B 2 3=(H:Int)+1) (h0 : HeightLe (mutate B 0) H) :
    0<B 0 2 ∧ B 0 3<0 ∧
      B 0 2≤(H:Int) ∧ -(H:Int)≤B 0 3 := by
  have h := (h0 2 3).2
  change B 2 3+correction (B 2 0) (B 0 3)≤(H:Int) at h
  have hp := correction_negative_inputs (B 2 0) (B 0 3)
    (show correction (B 2 0) (B 0 3)<0 by omega)
  have hb := hs 2 0
  have h02 := h0 0 2
  have h03 := h0 0 3
  change -(H:Int)≤ -B 0 2 ∧ -B 0 2≤(H:Int) at h02
  change -(H:Int)≤ -B 0 3 ∧ -B 0 3≤(H:Int) at h03
  omega

theorem positive_switch_two (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hf : B 2 3=(H:Int)+1) (h0 : HeightLe (mutate B 0) H)
    (h2 : HeightLe (mutate B 2) (H+1)) : B 0 2=1 := by
  obtain ⟨hb,hc,hbH,_⟩ := entry_paths B hs H hf h0
  have h := (h2 0 3).2
  change B 0 3+correction (B 0 2) (B 2 3)≤((H+1:Nat):Int) at h
  have he : correction (B 0 2) (B 2 3)=B 0 2*B 2 3 := by
    simp only [correction,max_eq_left (show 0≤B 0 2 by omega),
      max_eq_left (show 0≤B 2 3 by omega),max_eq_right (show -B 0 2≤0 by omega),
      max_eq_right (show -B 2 3≤0 by omega)]
    ring
  rw [he,hf] at h
  have h03 := h0 0 3
  change -(H:Int)≤ -B 0 3 ∧ -B 0 3≤(H:Int) at h03
  by_contra hh
  have hb2 : 2≤B 0 2 := by omega
  have hp := mul_nonneg (show 0≤B 0 2-2 by omega) (show 0≤(H:Int)+1 by omega)
  simp only [Nat.cast_add,Nat.cast_one] at h
  nlinarith

theorem positive_switch_three (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hf : B 2 3=(H:Int)+1) (h0 : HeightLe (mutate B 0) H)
    (h3 : HeightLe (mutate B 3) (H+1)) : B 0 3= -1 := by
  obtain ⟨hb,hc,hbH,_⟩ := entry_paths B hs H hf h0
  have h := (h3 0 2).1
  change -((H+1:Nat):Int)≤B 0 2+correction (B 0 3) (B 3 2) at h
  have h32 := hs 3 2
  have he : correction (B 0 3) (B 3 2)= -B 0 3*B 3 2 := by
    simp only [correction,max_eq_right (show B 0 3≤0 by omega),
      max_eq_right (show B 3 2≤0 by omega),max_eq_left (show 0≤ -B 0 3 by omega),
      max_eq_left (show 0≤ -B 3 2 by omega)]
    ring
  rw [he,h32,hf] at h
  by_contra hh
  have hc2 : B 0 3≤ -2 := by omega
  have hp := mul_nonneg (show 0≤ -B 0 3-2 by omega) (show 0≤(H:Int)+1 by omega)
  simp only [Nat.cast_add,Nat.cast_one] at h
  nlinarith

theorem switch_forces_unit (B : Matrix 4) (hs : SkewSymmetric B) (H : Nat)
    (hf : abs (B 2 3)=(H:Int)+1) (h0 : HeightLe (mutate B 0) H)
    (k : Fin 4) (hk : k=2 ∨ k=3) (hflat : HeightLe (mutate B k) (H+1)) :
    abs (B 0 k)=1 := by
  rcases le_total 0 (B 2 3) with hp|hn
  · rw [abs_of_nonneg hp] at hf
    rcases hk with rfl|rfl
    · rw [positive_switch_two B hs H hf h0 hflat]
      decide
    · rw [positive_switch_three B hs H hf h0 hflat]
      decide
  · have hfr : reverse B 2 3=(H:Int)+1 := by
      rw [abs_of_nonpos hn] at hf
      exact hf
    have h0r : HeightLe (mutate (reverse B) 0) H := by
      rw [mutate_reverse]
      exact (Rank4Round2.heightLe_reverse_iff _ H).mpr h0
    have hkr : HeightLe (mutate (reverse B) k) (H+1) := by
      rw [mutate_reverse]
      exact (Rank4Round2.heightLe_reverse_iff _ (H+1)).mpr hflat
    have hr : abs (reverse B 0 k)=1 := by
      rcases hk with rfl|rfl
      · rw [positive_switch_two (reverse B) (reverse_skew B hs) H hfr h0r hkr]
        decide
      · rw [positive_switch_three (reverse B) (reverse_skew B hs) H hfr h0r hkr]
        decide
    simpa only [reverse,abs_neg] using hr

#print axioms entry_paths
#print axioms switch_forces_unit
end Rank4CoordinatorR2.FlatSwitch
