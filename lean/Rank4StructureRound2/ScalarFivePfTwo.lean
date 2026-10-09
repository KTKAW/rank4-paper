import Rank4StructureRound2.SuperScalarPeak
import Rank4CoordinatorR2.ScalarPathBudget

/-! The scalar5/Pfaffian-square4 endpoint exception has a finite closed
mutation core. Consequently an actual MA matrix with a supplied total
proper scalar5 and Pfaffian-square4 has all entries bounded by2. The
endpoint bridge is explicit; no converse to scalar admissibility is used. -/
namespace QuiverProofs.Rank4StructureRound2.ScalarFivePfTwo
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
open Rank4Coordinator Rank4CoordinatorR2
open Rank4ReviewRound2.PeakNormalization
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

def node (n : Fin 4) : Matrix 4 := match n.val with
  | 0 => ofSix (-2) 0 1 0 (-1) (-1)
  | 1 => ofSix (-1) (-1) 0 (-1) 1 (-1)
  | 2 => ofSix (-1) (-1) 0 0 (-1) 1
  | _ => ofSix (-2) 0 0 0 0 (-1)

def Core (B : Matrix 4) : Prop :=
  ∃ n : Fin 4, ∃ p : Relabeling 4, ∃ r : Bool, B=signedFrame (node n) p r

private theorem transitions : ∀ n : Fin 4, ∀ k : Fin 4,
    ∃ m : Fin 4, ∃ p : Fin 24, ∃ r : Bool, ∀ i j : Fin 4,
      mutate (node n) k i j=signedFrame (node m) (permutation p) r i j := by decide

private theorem positive_box : ∀ a b c d e f : Fin 3,
    Algebra.markov a.val b.val c.val d.val e.val f.val=5 →
    ((a.val:Int)*f.val-b.val*e.val+c.val*d.val)^2=4 →
    ∃ n : Fin 4, ∃ p : Fin 24, ∃ r : Bool, ∀ i j : Fin 4,
      ofSix a.val b.val c.val d.val e.val f.val i j=
        signedFrame (node n) (permutation p) r i j := by decide

private theorem nodes_below : ∀ n : Fin 4, HeightLe (node n) 2 := by decide

theorem frame_comp (B : Matrix 4) (p q : Relabeling 4) (r s : Bool) :
    signedFrame (signedFrame B p r) q s=signedFrame B (p.trans q) (r != s) := by
  funext i j
  cases r <;> cases s <;> simp [signedFrame,relabel,reverse,Relabeling.trans]

theorem core_frame (B : Matrix 4) (q : Relabeling 4) (s : Bool) (h : Core B) :
    Core (signedFrame B q s) := by
  obtain ⟨n,p,r,rfl⟩ := h
  exact ⟨n,p.trans q,r != s,frame_comp _ p q r s⟩

theorem core_closed (B : Matrix 4) (k : Fin 4) (h : Core B) : Core (mutate B k) := by
  obtain ⟨n,p,r,rfl⟩ := h
  rw [signedFrame_mutate]
  obtain ⟨m,q,s,he⟩ := transitions n (p.toFun k)
  have heq : mutate (node n) (p.toFun k)=signedFrame (node m) (permutation q) s := by
    funext i j;exact he i j
  rw [heq]
  exact core_frame _ p r ⟨m,permutation q,s,rfl⟩

theorem core_word (B : Matrix 4) (w : List (Fin 4)) (h : Core B) : Core (applyWord B w) := by
  induction w generalizing B with
  | nil => exact h
  | cons k w ih => exact ih (mutate B k) (core_closed B k h)

theorem core_below (B : Matrix 4) (h : Core B) : HeightLe B 2 := by
  obtain ⟨n,p,r,rfl⟩ := h
  exact (signedFrame_height _ p r 2).mpr (nodes_below n)

theorem nonnegative_tuple_core (a b c d e f : Int)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e) (hf : 0≤f)
    (hm : Algebra.markov a b c d e f=5) (hpf : (a*f-b*e+c*d)^2=4) :
    Core (ofSix a b c d e f) := by
  obtain ⟨ha2,hb2,hc2,hd2,he2,hf2⟩ :=
    Algebra.coordinate_squares_le_markov a b c d e f ha hb hc hd he hf
  have hab : a≤2 := by nlinarith
  have hbb : b≤2 := by nlinarith
  have hcb : c≤2 := by nlinarith
  have hdb : d≤2 := by nlinarith
  have heb : e≤2 := by nlinarith
  have hfb : f≤2 := by nlinarith
  let aa : Fin 3 := ⟨a.toNat,by omega⟩
  let bb : Fin 3 := ⟨b.toNat,by omega⟩
  let cc : Fin 3 := ⟨c.toNat,by omega⟩
  let dd : Fin 3 := ⟨d.toNat,by omega⟩
  let ee : Fin 3 := ⟨e.toNat,by omega⟩
  let ff : Fin 3 := ⟨f.toNat,by omega⟩
  have ea : (aa.val:Int)=a := by dsimp [aa];omega
  have eb : (bb.val:Int)=b := by dsimp [bb];omega
  have ec : (cc.val:Int)=c := by dsimp [cc];omega
  have ed : (dd.val:Int)=d := by dsimp [dd];omega
  have eeq : (ee.val:Int)=e := by dsimp [ee];omega
  have ef : (ff.val:Int)=f := by dsimp [ff];omega
  have hs := positive_box aa bb cc dd ee ff
  rw [ea,eb,ec,ed,eeq,ef] at hs
  obtain ⟨n,p,r,heq⟩ := hs hm hpf
  exact ⟨n,permutation p,r,by funext i j;exact heq i j⟩

theorem actual_MA_scalar_five_pf_two_below (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hma : MutationAcyclic B)
    (p : CyclicOrder) (hp : TotalProper B p) (hm : orderMarkov B p=5)
    (hpf : (matrixPfaffian B)^2=4) : HeightLe B 2 := by
  obtain ⟨w,hw⟩ := hma
  obtain ⟨r,htr,hpr⟩ := totalProper_lifts_word B hs p hp w
  have hsC := word_preserves_skew B w hs
  obtain ⟨q,hq,hrq⟩ := hEnd _ hsC hw r hpr
  have hM := transport_markov hs htr
  have hMq := ProperWiggleInvariants.markov_wiggle_invariant _ hsC hrq
  let C := applyWord B w
  let D := relabel C q
  have hsD : SkewSymmetric D := relabel_skew C q hsC
  have hmD : Algebra.markov (D 0 1) (D 0 2) (D 0 3) (D 1 2) (D 1 3) (D 2 3)=5 := by
    change orderMarkov C q=5
    change orderMarkov C r=orderMarkov B p at hM
    change orderMarkov C r=orderMarkov C q at hMq
    omega
  have hpfD : (matrixPfaffian D)^2=4 := by
    calc
      (matrixPfaffian D)^2=(matrixPfaffian C)^2 := ClassSeparation.pfaffian_square_relabel C hsC q
      _=(matrixPfaffian B)^2 := pfaffian_square_word B w hs
      _=4 := hpf
  change ((D 0 1)*(D 2 3)-(D 0 2)*(D 1 3)+(D 0 3)*(D 1 2))^2=4 at hpfD
  have hD := nonnegative_tuple_core (D 0 1) (D 0 2) (D 0 3) (D 1 2) (D 1 3) (D 2 3)
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2 hmD hpfD
  rw [ofSix_reconstruct D hsD] at hD
  have hC := core_frame D q.symm false hD
  change Core (relabel (relabel C q) q.symm) at hC
  rw [relabel_inverse] at hC
  have hB := core_word C w.reverse hC
  rw [show C=applyWord B w from rfl,ScalarPathBudget.word_undo] at hB
  exact core_below B hB

#print axioms core_closed
#print axioms nonnegative_tuple_core
#print axioms actual_MA_scalar_five_pf_two_below
end QuiverProofs.Rank4StructureRound2.ScalarFivePfTwo
