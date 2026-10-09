import Rank4CoordinatorR2.EndpointBudget
import Rank4Round2.OverHeightCount
import Mathlib.Data.Nat.Find

/-! Existence of a lexicographically minimal actual acyclicizing witness.
Classical selection occurs only inside this erased existence proof and does
not supply a classifier or an executable search bound. -/
namespace Rank4CoordinatorR2
open QuiverProofs Rank4Coordinator Rank4Round2

theorem height_mono (B : Matrix 4) (H K : Nat) (hHK : H≤K) (h : HeightLe B H) :
    HeightLe B K := by
  intro i j
  have hb := h i j
  constructor <;> omega

theorem prefix_height_mono (B : Matrix 4) (w : List (Fin 4)) (H K : Nat)
    (hHK : H≤K) (h : PrefixHeightLe B w H) : PrefixHeightLe B w K := by
  intro u v he
  exact height_mono _ H K hHK (h u v he)

theorem every_word_has_prefix_bound (B : Matrix 4) (hB : SkewSymmetric B)
    (w : List (Fin 4)) : ∃ H, PrefixHeightLe B w H := by
  induction w generalizing B with
  | nil => exact ⟨entryBudget B,(prefixHeight_nil B _).mpr (entry_height_budget B hB)⟩
  | cons k w ih =>
    obtain ⟨H,hH⟩ := ih (mutate B k) (mutation_preserves_skew B k hB)
    refine ⟨entryBudget B+H,(prefixHeight_cons B k w _).mpr ⟨?_,?_⟩⟩
    · exact height_mono B _ _ (by omega) (entry_height_budget B hB)
    · exact prefix_height_mono _ w H _ (by omega) hH

theorem prefix_height_append_iff (B : Matrix 4) (u v : List (Fin 4)) (H : Nat) :
    PrefixHeightLe B (u++v) H ↔
      PrefixHeightLe B u H ∧ PrefixHeightLe (applyWord B u) v H := by
  constructor
  · intro h
    constructor
    · intro p q he
      exact h p (q++v) (by rw [he,List.append_assoc])
    · intro p q he
      have hh := h (u++p) q (by rw [he,List.append_assoc])
      rwa [applyWord_append] at hh
  · rintro ⟨hu,hv⟩
    exact prefixHeight_append B u v H hu hv

/-- The tertiary minimum removes immediate repeated mutations without
assuming a shortest witness independently of the height/count choices. -/
theorem profile_minimal_no_backtrack (B : Matrix 4) (M : Nat) (w : List (Fin 4))
    (ha : Acyclic (applyWord B w)) (hh : PrefixHeightLe B w M)
    (hcount : ∀ v, Acyclic (applyWord B v) → PrefixHeightLe B v M →
      overCount B w (M-1)≤overCount B v (M-1))
    (hlength : ∀ v, Acyclic (applyWord B v) → PrefixHeightLe B v M →
      overCount B v (M-1)=overCount B w (M-1) → w.length≤v.length) :
    ∀ u k v, w≠u++k::k::v := by
  intro u k v hw
  subst w
  have hend : applyWord B (u++k::k::v)=applyWord B (u++v) := by
    simp only [applyWord_append,applyWord,mutation_involutive]
  have han : Acyclic (applyWord B (u++v)) := hend ▸ ha
  obtain ⟨hu,ht⟩ := (prefix_height_append_iff B u (k::k::v) M).mp hh
  have hv := ((prefixHeight_cons _ k (k::v) M).mp ht).2
  have hv' := ((prefixHeight_cons _ k v M).mp hv).2
  rw [mutation_involutive] at hv'
  have hhn := prefixHeight_append B u v M hu hv'
  have hc := hcount (u++v) han hhn
  have hdrop : overCount B (u++k::k::v) (M-1)=
      overCount B (u++v) (M-1)+overBit (mutate (applyWord B u) k) (M-1)+
        overBit (applyWord B u) (M-1) := by
    simp only [overCount_append,overCount,mutation_involutive]
    omega
  have hceq : overCount B (u++v) (M-1)=overCount B (u++k::k::v) (M-1) := by omega
  have hl := hlength (u++v) han hhn hceq
  simp only [List.length_append,List.length_cons] at hl
  omega

/-- Height is minimized first, then the number of reached states at its
upper layer, then word length. Every selected object is a genuine finite
mutation word ending at an acyclic matrix. -/
theorem exists_profile_minimal_witness (B : Matrix 4) (hB : SkewSymmetric B)
    (hMA : MutationAcyclic B) :
    ∃ M : Nat, ∃ w : List (Fin 4),
      Acyclic (applyWord B w) ∧ PrefixHeightLe B w M ∧
      (∀ N v, Acyclic (applyWord B v) → PrefixHeightLe B v N → M≤N) ∧
      (∀ v, Acyclic (applyWord B v) → PrefixHeightLe B v M →
        overCount B w (M-1)≤overCount B v (M-1)) ∧
      (∀ v, Acyclic (applyWord B v) → PrefixHeightLe B v M →
        overCount B v (M-1)=overCount B w (M-1) → w.length≤v.length) := by
  classical
  obtain ⟨w0,ha0⟩ := hMA
  obtain ⟨H0,hh0⟩ := every_word_has_prefix_bound B hB w0
  let P : Nat → Prop := fun H => ∃ v, Acyclic (applyWord B v) ∧ PrefixHeightLe B v H
  have hex : ∃ H, P H := ⟨H0,w0,ha0,hh0⟩
  let M := Nat.find hex
  obtain ⟨w1,ha1,hh1⟩ := Nat.find_spec hex
  let C : Nat → Prop := fun c => ∃ v, Acyclic (applyWord B v) ∧
    PrefixHeightLe B v M ∧ overCount B v (M-1)=c
  have hcount : ∃ c, C c := ⟨overCount B w1 (M-1),w1,ha1,hh1,rfl⟩
  let c := Nat.find hcount
  obtain ⟨w2,ha2,hh2,hc2⟩ := Nat.find_spec hcount
  let L : Nat → Prop := fun l => ∃ v, Acyclic (applyWord B v) ∧
    PrefixHeightLe B v M ∧ overCount B v (M-1)=c ∧ v.length=l
  have hlength : ∃ l, L l := ⟨w2.length,w2,ha2,hh2,hc2,rfl⟩
  obtain ⟨w,ha,hh,hc,hl⟩ := Nat.find_spec hlength
  refine ⟨M,w,ha,hh,?_,?_,?_⟩
  · intro N v hav hhv
    exact Nat.find_min' hex ⟨v,hav,hhv⟩
  · intro v hav hhv
    rw [hc]
    exact Nat.find_min' hcount ⟨v,hav,hhv,rfl⟩
  · intro v hav hhv hcv
    rw [hl]
    exact Nat.find_min' hlength ⟨v,hav,hhv,hcv.trans hc,rfl⟩

#print axioms every_word_has_prefix_bound
#print axioms profile_minimal_no_backtrack
#print axioms exists_profile_minimal_witness
end Rank4CoordinatorR2
