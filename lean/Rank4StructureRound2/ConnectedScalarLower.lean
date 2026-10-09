import Rank4StructureRound2.ScalarFivePfTwo

/-! Exact connected proper scalar lower bound with explicit endpoint bridge.
A nonnegative four-vertex tuple of scalar<=2 has all entries<=1 and the
complete Fin2 box has disconnected support. No numerical search is used. -/
namespace QuiverProofs.Rank4StructureRound2.ConnectedScalarLower
open Census ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 8000000

private theorem small_box : ∀ a b c d e f : Fin 2,
    Algebra.markov a.val b.val c.val d.val e.val f.val≤2 →
    ¬ConnectedSupport (ofSix a.val b.val c.val d.val e.val f.val) := by decide

theorem nonnegative_small_disconnected (a b c d e f : Int)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e) (hf : 0≤f)
    (hm : Algebra.markov a b c d e f≤2) : ¬ConnectedSupport (ofSix a b c d e f) := by
  obtain ⟨ha2,hb2,hc2,hd2,he2,hf2⟩:=
    Algebra.coordinate_squares_le_markov a b c d e f ha hb hc hd he hf
  have hab : a≤1 := by nlinarith
  have hbb : b≤1 := by nlinarith
  have hcb : c≤1 := by nlinarith
  have hdb : d≤1 := by nlinarith
  have heb : e≤1 := by nlinarith
  have hfb : f≤1 := by nlinarith
  let aa : Fin 2:=⟨a.toNat,by omega⟩
  let bb : Fin 2:=⟨b.toNat,by omega⟩
  let cc : Fin 2:=⟨c.toNat,by omega⟩
  let dd : Fin 2:=⟨d.toNat,by omega⟩
  let ee : Fin 2:=⟨e.toNat,by omega⟩
  let ff : Fin 2:=⟨f.toNat,by omega⟩
  have ea : (aa.val:Int)=a := by dsimp [aa];omega
  have eb : (bb.val:Int)=b := by dsimp [bb];omega
  have ec : (cc.val:Int)=c := by dsimp [cc];omega
  have ed : (dd.val:Int)=d := by dsimp [dd];omega
  have eeq : (ee.val:Int)=e := by dsimp [ee];omega
  have ef : (ff.val:Int)=f := by dsimp [ff];omega
  have hs:=small_box aa bb cc dd ee ff
  rw [ea,eb,ec,ed,eeq,ef] at hs
  exact hs hm

theorem actual_connected_scalar_three (hEnd : EndpointTopological4)
    (B : Matrix 4) (hs : SkewSymmetric B) (hconn : ConnectedSupport B)
    (hma : MutationAcyclic B) (p : CyclicOrder) (hp : TotalProper B p) :
    3≤orderMarkov B p := by
  by_contra hbad
  obtain ⟨w,hw⟩:=hma
  obtain ⟨r,htr,hpr⟩:=totalProper_lifts_word B hs p hp w
  have hsC:=word_preserves_skew B w hs
  obtain ⟨q,hq,hrq⟩:=hEnd _ hsC hw r hpr
  have hM:=transport_markov hs htr
  have hMq:=ProperWiggleInvariants.markov_wiggle_invariant _ hsC hrq
  let C:=applyWord B w
  let D:=relabel C q
  have hsD : SkewSymmetric D:=relabel_skew C q hsC
  have hmD : Algebra.markov (D 0 1) (D 0 2) (D 0 3) (D 1 2) (D 1 3) (D 2 3)≤2 := by
    change orderMarkov C q≤2
    change orderMarkov C r=orderMarkov B p at hM
    change orderMarkov C r=orderMarkov C q at hMq
    omega
  have hn:=nonnegative_small_disconnected _ _ _ _ _ _
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2 hmD
  change ¬ConnectedSupport (ofSix (D 0 1) (D 0 2) (D 0 3) (D 1 2) (D 1 3) (D 2 3)) at hn
  rw [ofSix_reconstruct D hsD] at hn
  exact hn (connected_relabel C q (connected_applyWord B w hconn))

#print axioms nonnegative_small_disconnected
#print axioms actual_connected_scalar_three
end QuiverProofs.Rank4StructureRound2.ConnectedScalarLower
