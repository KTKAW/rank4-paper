import Rank4Round2.ZeroSquare
import Rank4Round2.UnitDetour

/-! Fixed-ceiling path progress for successful guarded local detours.
The count includes every reached state, excluding the common starting state.
These lemmas provide actual local progress, not a supplier of the guards or
a plateau-lowering theorem for arbitrary MA witnesses.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator

def overBit (B : Matrix 4) (H : Nat) : Nat := if HeightLe B H then 0 else 1

def overCount (B : Matrix 4) : List (Fin 4) → Nat → Nat
  | [], _ => 0
  | k::w, H => overBit (mutate B k) H + overCount (mutate B k) w H

theorem overBit_relabel (B : Matrix 4) (p : Relabeling 4) (H : Nat) :
    overBit (relabel B p) H = overBit B H := by
  simp only [overBit,heightLe_relabel_iff]

theorem overCount_relabel (B : Matrix 4) (p : Relabeling 4)
    (w : List (Fin 4)) (H : Nat) :
    overCount (relabel B p) (w.map p.invFun) H = overCount B w H := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    simp only [List.map_cons,overCount,mutate_relabel,p.right_inv,overBit_relabel,ih]

theorem overCount_append (B : Matrix 4) (u v : List (Fin 4)) (H : Nat) :
    overCount B (u++v) H = overCount B u H + overCount (applyWord B u) v H := by
  induction u generalizing B with
  | nil => simp only [List.nil_append,overCount,applyWord,Nat.zero_add]
  | cons k u ih =>
    simp only [List.cons_append,overCount,applyWord,ih,Nat.add_assoc]

theorem overCount_eq_zero (B : Matrix 4) (w : List (Fin 4)) (H : Nat)
    (h : PrefixHeightLe B w H) : overCount B w H = 0 := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih =>
    have ht := ((prefixHeight_cons B k w H).mp h).2
    have hm : HeightLe (mutate B k) H := ht [] w rfl
    simp only [overCount,overBit,if_pos hm,ih _ ht,Nat.zero_add]

/-- A bounded replacement removes the unique over-ceiling parent and leaves
the entire remaining suffix count unchanged, including when relabeled. -/
theorem strict_peak_overCount (P : Matrix 4) (i j : Fin 4)
    (new tail : List (Fin 4)) (p : Relabeling 4) (H : Nat)
    (hP : ¬HeightLe P H) (hR : HeightLe (mutate P j) H)
    (he : applyWord (mutate P i) new = relabel (mutate P j) p)
    (hn : PrefixHeightLe (mutate P i) new H) :
    overCount (mutate P i) (new++tail.map p.invFun) H + 1 =
      overCount (mutate P i) ([i,j]++tail) H := by
  rw [overCount_append,he,overCount_relabel,overCount_eq_zero _ _ _ hn,
    overCount_append]
  simp only [overCount,applyWord,mutation_involutive,overBit,if_neg hP,if_pos hR]
  omega

theorem strict_peak_reroute (P : Matrix 4) (i j : Fin 4)
    (new tail : List (Fin 4)) (p : Relabeling 4) (H : Nat)
    (hP : ¬HeightLe P H) (hR : HeightLe (mutate P j) H)
    (he : applyWord (mutate P i) new = relabel (mutate P j) p)
    (hn : PrefixHeightLe (mutate P i) new H)
    (ha : Acyclic (applyWord (mutate P i) ([i,j]++tail))) :
    Acyclic (applyWord (mutate P i) (new++tail.map p.invFun)) ∧
      overCount (mutate P i) (new++tail.map p.invFun) H <
        overCount (mutate P i) ([i,j]++tail) H := by
  have hend : applyWord (mutate P i) new =
      relabel (applyWord (mutate P i) [i,j]) p := by
    simpa only [applyWord,mutation_involutive] using he
  constructor
  · rw [reroute_endpoint _ [i,j] new tail p hend]
    exact (acyclic_relabel_iff _ p).mpr ha
  · have h := strict_peak_overCount P i j new tail p H hP hR he hn
    omega

/-- The exact zero-edge guard supplies a successful local replacement. -/
theorem zeroPeak_count_decrease (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H)
    (hP : ¬HeightLe (zeroPeak b c d e f) H)
    (guard : -(H:Int)≤f-b*c-d*e ∧ f-b*c-d*e≤(H:Int))
    (tail : List (Fin 4)) :
    overCount (mutate (zeroPeak b c d e f) 0) ([1,0]++tail) H + 1 =
      overCount (mutate (zeroPeak b c d e f) 0) ([0,1]++tail) H := by
  have hn := (zeroPeak_detour_iff b c d e f H hb hc hd he h0 h1).mpr guard
  have hend := zero_square_endpoint (zeroPeak b c d e f)
    (ofSix_skew _ _ _ _ _ _) (by simp [zeroPeak,ofSix])
  rw [overCount_append,overCount_eq_zero _ _ _ hn,hend,overCount_append]
  simp only [overCount,applyWord,mutation_involutive,overBit,if_neg hP,if_pos h1]
  omega

theorem unitPeak_count_decrease (b c d e f : Int) (H : Nat)
    (hb : 0<b) (hc : 0<c) (hd : 0<d) (he : 0<e)
    (h0 : HeightLe (mutate (unitPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (unitPeak b c d e f) 1) H)
    (hP : ¬HeightLe (unitPeak b c d e f) H)
    (guard : -(H:Int)≤f-unitCost b c d e) (tail : List (Fin 4)) :
    overCount (mutate (unitPeak b c d e f) 0)
        ([1,0,1]++tail.map Forks.swap01.invFun) H + 1 =
      overCount (mutate (unitPeak b c d e f) 0) ([0,1]++tail) H := by
  exact strict_peak_overCount _ 0 1 [1,0,1] tail Forks.swap01 H hP h1
    (unitPeak_detour_endpoint b c d e f hb hc hd he)
    ((unitPeak_detour_iff b c d e f H hb hc hd he h0 h1).mpr guard)

#print axioms overCount
#print axioms strict_peak_reroute
#print axioms zeroPeak_count_decrease
#print axioms unitPeak_count_decrease
end Rank4Round2
