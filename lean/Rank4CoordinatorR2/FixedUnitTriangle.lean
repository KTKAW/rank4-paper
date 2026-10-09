import Rank4CoordinatorR2.MixedUnitIncident
import Rank4Round2.MixedUnitFamily
import Rank4StructureRound2.MixedUnitHeight

/-! Fixed (1,-2,1) triangle: the first three ceiling steps force the
explicit mixed family above the proper scalar budget. Its next two
nonbacktracking ceiling steps are forced. All-sign triangle entry is
separate; these statements retain the triangle representation. -/
namespace Rank4CoordinatorR2.FixedUnitTriangle
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperMutation ProperWiggle
open QuiverProofs.Rank4StructureRound2.MixedUnitHeight
set_option maxHeartbeats 4000000
private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem family_shape (c e f : Int) (H : Nat)
    (hR : HeightLe (R c e f) H)
    (hPath : PrefixHeightLe (R c e f) [0,1,2] (H+1))
    (hFirst : ¬HeightLe (mutate (R c e f) 0) H)
    (p : CyclicOrder) (hp : ProperClass (R c e f) p)
    (hM : orderMarkov (R c e f) p≤(H:Int)) :
    1≤c ∧ c≤(H:Int) ∧ e=0 ∧ f=(H:Int)+1-2*c := by
  obtain ⟨h1,h2,h3,_⟩ := matrices c e f
  have hP : HeightLe (O1 c e f) (H+1) := by rw [←h1];exact hPath [0] [1,2] rfl
  have hS : HeightLe (O2 c e f) (H+1) := by rw [←h2,←h1];exact hPath [0,1] [2] rfl
  have hT : HeightLe (O3 c e f) (H+1) := by rw [←h3,←h2,←h1];exact hPath [0,1,2] [] (by simp)
  rw [h1] at hFirst
  have hH := hR 0 2
  have hc := hR 0 3
  have he := hR 1 3
  have hf := hR 2 3
  simp only [R,ofSix] at hH hc he hf
  have hH2 : 2≤H := by omega
  have hPos : 0<c := by
    by_contra hn
    have hc0 : c≤0 := by omega
    have hpc : pos c=0 := by unfold pos;omega
    have hnc : neg c= -c := by unfold neg;omega
    have hl : e-neg c= -((H:Int)+1) := by
      have hEdge := hP 1 3
      simp only [O1,ofSix,Nat.cast_add,Nat.cast_one] at hEdge
      by_contra hn
      apply hFirst
      intro i j
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
        simp only [O1,ofSix,hpc,hnc] <;> omega
    have hC : c<0 := by rw [hnc] at hl;omega
    have hpf : pos f=0 := by
      have hEdge := (hT 1 3).2
      simp only [O3,ofSix,hl,hpc,show pos (-((H:Int)+1))=0 by unfold pos;omega,
        Nat.cast_add,Nat.cast_one] at hEdge
      unfold pos at hEdge ⊢
      omega
    have hf0 : f≤0 := by unfold pos at hpf;omega
    have hrep : R c e f=MixedUnitIncident.peak (-c) f ((H:Int)+1) := by
      rw [hnc] at hl
      have heq : e= -c-((H:Int)+1) := by omega
      simp [R,MixedUnitIncident.peak,heq]
    have hHuge := MixedUnitIncident.proper_scalar_exceeds (-c) f ((H:Int)+1)
      (by omega) (by omega) (by omega) hf0 p (by rwa [←hrep])
    rw [←hrep] at hHuge
    omega
  have hpc : pos c=c := by unfold pos;omega
  have hnc : neg c=0 := by unfold neg;omega
  have hTop : f+2*c=(H:Int)+1 := by
    have hEdge := hP 2 3
    simp only [O1,ofSix,hpc,Nat.cast_add,Nat.cast_one] at hEdge
    by_contra hn
    apply hFirst
    intro i j
    rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp only [O1,ofSix,hpc,hnc] <;> omega
  have he0 : e≤0 := by
    have hEdge := (hS 2 3).2
    simp only [O2,ofSix,hnc,sub_zero,hpc,hTop,Nat.cast_add,Nat.cast_one] at hEdge
    unfold pos at hEdge
    omega
  have hpe : pos e=0 := by unfold pos;omega
  have he0' : 0≤e := by
    have hEdge := (hT 1 3).2
    simp only [O3,ofSix,hnc,sub_zero,hpc,hTop,hpe,add_zero,
      show pos ((H:Int)+1)=(H:Int)+1 by unfold pos;omega,
      Nat.cast_add,Nat.cast_one] at hEdge
    omega
  exact ⟨by omega,hc.2,by omega,by omega⟩

theorem third_forward_only (H : Nat) (c : Int) (hH : 2≤H)
    (hc : 1≤c) (hcH : c≤(H:Int)) (k : Fin 4) (hk : k≠2)
    (hNext : HeightLe (mutate (MixedUnitFamily.O3 H c) k) (H+1)) : k=0 := by
  rcases four k with rfl|rfl|rfl|rfl
  · rfl
  · have h := (hNext 0 3).2
    simp [MixedUnitFamily.O3,mutate,ofSix,correction,
      max_eq_left (show 0≤(H:Int)+1 by omega),
      max_eq_right (show -((H:Int)+1)≤0 by omega)] at h
    omega
  · exact False.elim (hk rfl)
  · have h := (hNext 1 2).2
    simp [MixedUnitFamily.O3,mutate,ofSix,correction,
      max_eq_left (show 0≤(H:Int)+1 by omega),
      max_eq_right (show -((H:Int)+1)≤0 by omega)] at h
    nlinarith

theorem fourth_forward_only (H : Nat) (c : Int) (hH : 2≤H)
    (hc : 1≤c) (hcH : c≤(H:Int)) (k : Fin 4) (hk : k≠0)
    (hNext : HeightLe (mutate (MixedUnitFamily.O4 H c) k) (H+1)) : k=2 := by
  rcases four k with rfl|rfl|rfl|rfl
  · exact False.elim (hk rfl)
  · have h := (hNext 2 3).2
    simp [MixedUnitFamily.O4,mutate,ofSix,correction,
      max_eq_left (show 0≤(H:Int)+1 by omega),
      max_eq_right (show -((H:Int)+1)≤0 by omega)] at h
    omega
  · rfl
  · have h := (hNext 0 1).1
    simp [MixedUnitFamily.O4,mutate,ofSix,correction,
      max_eq_left (show 0≤(H:Int)+1-c by omega),
      max_eq_left (show 0≤(H:Int)+1 by omega),
      max_eq_right (show c-((H:Int)+1)≤0 by omega),
      max_eq_right (show -((H:Int)+1)≤0 by omega)] at h
    have hmul := mul_nonneg (show 0≤(H:Int)+1 by omega) (show 0≤(H:Int)-c by omega)
    nlinarith

#print axioms family_shape
#print axioms third_forward_only
#print axioms fourth_forward_only
end Rank4CoordinatorR2.FixedUnitTriangle
