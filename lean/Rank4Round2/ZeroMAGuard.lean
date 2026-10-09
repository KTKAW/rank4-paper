import Rank4Round2.OverHeightCount
import Rank4CoordinatorR2.ZeroScalar

/-! Min-2 incident zero-pivot MA peaks admit the actual commutative square.
The two properness bridges remain explicit; incident-unit peaks are outside
this statement. The unchanged endpoint preserves the entire suffix.
-/
namespace Rank4Round2
open QuiverProofs Rank4Coordinator Census ProperObstructionSoundness

theorem zeroPeak_one (b c d e f : Int) (hd : 0<d) (he : 0<e) :
    mutate (zeroPeak b c d e f) 1 = ofSix 0 b (-c) (-d) e (f-d*e) := by
  funext i j
  have four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [zeroPeak,mutate,ofSix,correction] <;> grind

theorem zero_ma_square_guard
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hma : MutationAcyclic (zeroPeak b c d e f)) :
    PrefixHeightLe (mutate (zeroPeak b c d e f) 0) [1,0] H := by
  have hc0 := h0 2 3
  have hc1 := h1 2 3
  rw [zeroPeak_zero b c d e f (by omega) (by omega)] at hc0
  rw [zeroPeak_one b c d e f (by omega) (by omega)] at hc1
  simp only [ofSix] at hc0 hc1
  exact (zeroPeak_detour_iff b c d e f H (by omega) (by omega) (by omega)
    (by omega) h0 h1).mpr
    (Rank4CoordinatorR2.zeroPeak_MA_square_guard hExist hEnd b c d e f H
      hb hc hd he hf hc0.1 hc0.2 hc1.1 hc1.2 hma)

theorem zero_ma_square_count_decrease
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (hma : MutationAcyclic (zeroPeak b c d e f))
    (tail : List (Fin 4)) :
    overCount (mutate (zeroPeak b c d e f) 0) ([1,0]++tail) H + 1 =
      overCount (mutate (zeroPeak b c d e f) 0) ([0,1]++tail) H := by
  have hn := zero_ma_square_guard hExist hEnd b c d e f H hb hc hd he h0 h1 hf hma
  apply zeroPeak_count_decrease b c d e f H (by omega) (by omega) (by omega)
    (by omega) h0 h1 _
    ((zeroPeak_detour_iff b c d e f H (by omega) (by omega) (by omega)
      (by omega) h0 h1).mp hn) tail
  intro hP
  have h := (hP 2 3).2
  change f≤(H:Int) at h
  omega

theorem zero_ma_square_acyclic_reroute
    (hExist : MAHasTotalProper4) (hEnd : EndpointTopological4)
    (b c d e f : Int) (H : Nat)
    (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (he : 2≤e)
    (h0 : HeightLe (mutate (zeroPeak b c d e f) 0) H)
    (h1 : HeightLe (mutate (zeroPeak b c d e f) 1) H)
    (hf : (H:Int)<f) (tail : List (Fin 4))
    (ha : Acyclic (applyWord (mutate (zeroPeak b c d e f) 0) ([0,1]++tail))) :
    Acyclic (applyWord (mutate (zeroPeak b c d e f) 0) ([1,0]++tail)) ∧
      overCount (mutate (zeroPeak b c d e f) 0) ([1,0]++tail) H <
        overCount (mutate (zeroPeak b c d e f) 0) ([0,1]++tail) H := by
  have hmaL : MutationAcyclic (mutate (zeroPeak b c d e f) 0) := ⟨[0,1]++tail,ha⟩
  have hma := (mutationAcyclic_iff _ 0).mp hmaL
  constructor
  · rw [applyWord_append,zero_square_endpoint (zeroPeak b c d e f) (ofSix_skew _ _ _ _ _ _)
      (show zeroPeak b c d e f 0 1=0 from rfl)]
    simpa only [applyWord_append,applyWord,mutation_involutive] using ha
  · have h := zero_ma_square_count_decrease hExist hEnd b c d e f H
      hb hc hd he h0 h1 hf hma tail
    omega

#print axioms zero_ma_square_guard
#print axioms zero_ma_square_count_decrease
#print axioms zero_ma_square_acyclic_reroute
end Rank4Round2
