import Rank4Round2.MixedUnitFrame

/-! Exact endpoint covariance on the original labels. The common arrow
reversal cancels, leaving the conjugate of the endpoint cycle. -/
namespace Rank4Round2.MixedUnitActualEndpoint
open QuiverProofs Rank4Coordinator Rank4Round2 MixedUnitRelation MixedUnitFrame
open Rank4ReviewRound2.PeakNormalization

def conjugate (p q : Relabeling 4) : Relabeling 4 := (p.trans q).trans p.symm

theorem signedFrame_inverse (B : Matrix 4) (p : Relabeling 4) (r : Bool) :
    signedFrame (signedFrame B p r) p.symm r=B := by
  cases r <;> funext i j <;>
    simp [signedFrame,relabel,Relabeling.symm,reverse,p.right_inv]

theorem signedFrame_injective (A B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (h : signedFrame A p r=signedFrame B p r) : A=B := by
  have hh := congrArg (fun D => signedFrame D p.symm r) h
  dsimp only at hh
  rwa [signedFrame_inverse,signedFrame_inverse] at hh

theorem covariance (A B : Matrix 4) (p q : Relabeling 4) (r : Bool)
    (h : signedFrame A p r=relabel (signedFrame B p r) q) :
    A=relabel B (conjugate p q) := by
  apply signedFrame_injective A (relabel B (conjugate p q)) p r
  rw [h]
  cases r <;> funext i j <;>
    simp [signedFrame,relabel,conjugate,Relabeling.trans,Relabeling.symm,
      Function.comp_def,reverse,p.left_inv]

theorem actual_tail_word (p : Relabeling 4) (tail : List (Fin 4)) :
    newFrame p tail=new.map p.toFun++tail.map (conjugate p cycle).invFun := by
  simp [newFrame,List.map_append,List.map_map,conjugate,Relabeling.trans,
    Relabeling.symm,Function.comp_def]

theorem actual_endpoint (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (c e f : Int) (hrep : signedFrame B p r=R c e f) (tail : List (Fin 4)) :
    applyWord B (newFrame p tail)=
      relabel (applyWord B (oldFrame p tail)) (conjugate p cycle) :=
  covariance _ _ p cycle r (endpoint B p r c e f hrep tail)

theorem actual_tail_endpoint (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (c e f : Int) (hrep : signedFrame B p r=R c e f) (tail : List (Fin 4)) :
    applyWord B (new.map p.toFun++tail.map (conjugate p cycle).invFun)=
      relabel (applyWord B (old.map p.toFun++tail)) (conjugate p cycle) := by
  simpa only [oldFrame_eq,actual_tail_word] using actual_endpoint B p r c e f hrep tail

theorem actual_acyclic (B : Matrix 4) (p : Relabeling 4) (r : Bool)
    (c e f : Int) (hrep : signedFrame B p r=R c e f) (tail : List (Fin 4))
    (ha : Acyclic (applyWord B (oldFrame p tail))) :
    Acyclic (applyWord B (newFrame p tail)) := by
  rw [actual_endpoint B p r c e f hrep tail]
  exact (acyclic_relabel_iff _ (conjugate p cycle)).mpr ha

#print axioms covariance
#print axioms actual_tail_endpoint
#print axioms actual_acyclic
end Rank4Round2.MixedUnitActualEndpoint
