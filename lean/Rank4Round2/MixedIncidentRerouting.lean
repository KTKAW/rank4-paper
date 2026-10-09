import Rank4StructureRound2.MixedIncidentFamilyHeight
import Rank4Round2.MixedUnitReverseRelation

/-! Both other-phase replacement routes have the same endpoint cycle.
The general signed whole-word consumer transforms the literal actual tail
by the conjugate inverse cycle and preserves its high-state count. -/
namespace Rank4Round2.MixedIncidentRerouting
open QuiverProofs Rank4Coordinator Rank4Round2 MixedUnitRelation
open Rank4ReviewRound2.PeakNormalization MixedUnitActualEndpoint
open QuiverProofs.Rank4StructureRound2

def second : List (Fin 4) := [2,0,2,1,0]

theorem second_endpoint (t u F : Int) (ht : 1≤t) (hu : 1≤u)
    (htF : t≤F-1) (huF : u≤F-1) :
    applyWord (MixedIncidentFamilyHeight.R t u F) second=
      relabel (applyWord (MixedIncidentFamilyHeight.R t u F) MixedUnitReverseRelation.short) cycle := by
  obtain ⟨ha1,ha2,ha3,ha4,ha5,hb1,hb2,hb3,hb4,hb5⟩ :=
    MixedIncidentFamilyHeight.matrices t u F ht hu htF huF
  have hA : applyWord (MixedIncidentFamilyHeight.R t u F) MixedUnitReverseRelation.long=
      MixedIncidentFamilyHeight.E t u F := by
    simp only [MixedUnitReverseRelation.long,applyWord,ha1,ha2,ha3,ha4,ha5]
  have hB : applyWord (MixedIncidentFamilyHeight.R t u F) second=
      MixedIncidentFamilyHeight.E t u F := by
    simp only [second,applyWord,hb1,hb2,hb3,hb4,hb5]
  rw [hB,←hA]
  exact MixedUnitReverseRelation.endpoint (-t) (t-F) (F-u)

theorem whole_signed_progress (B : Matrix 4) (lead tail : List (Fin 4))
    (p : Relabeling 4) (r : Bool) (old new : List (Fin 4)) (q : Relabeling 4) (H : Nat)
    (he : applyWord (signedFrame (applyWord B lead) p r) new=
      relabel (applyWord (signedFrame (applyWord B lead) p r) old) q)
    (hn : PrefixHeightLe (signedFrame (applyWord B lead) p r) new H)
    (hc : 0<overCount (applyWord B lead) (old.map p.toFun) H)
    (hw : PrefixHeightLe B (lead++(old.map p.toFun++tail)) (H+1))
    (ha : Acyclic (applyWord B (lead++(old.map p.toFun++tail)))) :
    PrefixHeightLe B (lead++(new.map p.toFun++tail.map (conjugate p q).invFun)) (H+1) ∧
    Acyclic (applyWord B (lead++(new.map p.toFun++tail.map (conjugate p q).invFun))) ∧
    overCount B (lead++(new.map p.toFun++tail.map (conjugate p q).invFun)) H<
      overCount B (lead++(old.map p.toFun++tail)) H := by
  have hLocal : applyWord (applyWord B lead) (new.map p.toFun)=
      relabel (applyWord (applyWord B lead) (old.map p.toFun)) (conjugate p q) := by
    apply covariance _ _ p q r
    simpa only [signedFrame_word] using he
  have hnActual := (signedFrame_forward_prefix (applyWord B lead) p r new H).mp hn
  have hParts := (prefixHeight_append_iff B lead (old.map p.toFun++tail) (H+1)).mp hw
  have hTail := ((prefixHeight_append_iff (applyWord B lead) (old.map p.toFun) tail
    (H+1)).mp hParts.2).2
  have hNew := reroute_prefixHeight (applyWord B lead) (old.map p.toFun) (new.map p.toFun)
    tail (conjugate p q) (H+1) hLocal
    (prefixHeight_mono _ _ H (H+1) (by omega) hnActual) hTail
  refine ⟨(prefixHeight_append_iff B lead _ (H+1)).mpr ⟨hParts.1,hNew⟩,?_,?_⟩
  · rw [applyWord_append,reroute_endpoint _ _ _ _ _ hLocal,←applyWord_append]
    exact (acyclic_relabel_iff _ (conjugate p q)).mpr ha
  · have hCount : overCount (applyWord (applyWord B lead) (new.map p.toFun))
        (tail.map (conjugate p q).invFun) H=
        overCount (applyWord (applyWord B lead) (old.map p.toFun)) tail H := by
      rw [hLocal,overCount_relabel]
    have hZero := overCount_eq_zero _ _ H hnActual
    simp only [overCount_append]
    rw [hCount,hZero]
    omega

theorem whole_signed_count (B : Matrix 4) (lead tail : List (Fin 4))
    (p : Relabeling 4) (r : Bool) (old new : List (Fin 4)) (q : Relabeling 4) (H : Nat)
    (he : applyWord (signedFrame (applyWord B lead) p r) new=
      relabel (applyWord (signedFrame (applyWord B lead) p r) old) q) :
    overCount B (lead++(new.map p.toFun++tail.map (conjugate p q).invFun)) H+
        overCount (applyWord B lead) (old.map p.toFun) H=
      overCount B (lead++(old.map p.toFun++tail)) H+
        overCount (applyWord B lead) (new.map p.toFun) H := by
  have hLocal : applyWord (applyWord B lead) (new.map p.toFun)=
      relabel (applyWord (applyWord B lead) (old.map p.toFun)) (conjugate p q) := by
    apply covariance _ _ p q r
    simpa only [signedFrame_word] using he
  simp only [overCount_append]
  rw [hLocal,overCount_relabel]
  omega

#print axioms second_endpoint
#print axioms whole_signed_progress
#print axioms whole_signed_count
end Rank4Round2.MixedIncidentRerouting
