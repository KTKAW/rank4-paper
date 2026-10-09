import Rank4CoordinatorR2.Foundation
import QuiverProofs.ChamberProperness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A normalized three-high unit-prefix barrier. The two possible last
high walls have either negative proper scalar or a Pfaffian larger than
the permitted scalar budget. The all-sign geometric supplier is separate. -/
namespace Rank4CoordinatorR2.UnitThreeScalar
open QuiverProofs Rank4Coordinator Rank4CoordinatorR2 Rank4Round2
open ProperOrder ProperWiggle ProperMutation ProperObstructionSoundness
set_option maxHeartbeats 4000000

def scalar (b c d E F : Int) : Int :=
  1+b*b+c*c+d*d+E*E+c*E-b*d+F*F-F*(b*c+d*E)
def pf (b c d E F : Int) : Int := F-b*(c+E)+c*d
def root (b c d E F : Int) : Matrix 4 := ofSix 1 (-b) c d (-E) (F-b*c)

theorem incident_wall_large_pf (b c d E F : Int)
    (hF : 2≤F) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E)
    (hbd : d<b) (hbc : b*c≤2*F-1) (hCross : 2*F<b*c+d*E)
    (hWall : c+E=F) : F-1<2*abs (pf b c d E F) := by
  have hb3 : 3≤b := by
    by_contra hn
    have hb2 : b=2 := by omega
    have hd1 : d=1 := by omega
    rw [hb2,hd1] at hCross
    nlinarith
  let K := 2*b*b-3*b-4*d
  have hbk := mul_nonneg (show 0≤b-3 by omega) (show 0≤2*b-1 by omega)
  have hK : 1≤K := by dsimp [K];nlinarith
  have hFK := mul_nonneg (show 0≤F by omega) (show 0≤K-1 by omega)
  have hD := mul_nonneg (show 0≤2*d by omega) (show 0≤2*F-b*c-1 by omega)
  have heq : b*(2*(-pf b c d E F)-F)=F*K+2*d*(2*F-b*c) := by
    unfold pf
    rw [hWall]
    dsimp [K]
    ring
  have hPos : 0<2*(-pf b c d E F)-F := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (show 0≤b by omega)
      (show 2*(-pf b c d E F)-F≤0 by omega)
    nlinarith
  have hh := neg_le_abs (pf b c d E F)
  omega

theorem opposite_wall_negative_scalar (b c d E F : Int)
    (hF : 2≤F) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E)
    (hbF : b≤F-1) (hdF : d≤F-1) (hL : c+E≤F-1)
    (hbd : d<b) (hWall : d*(c+E)=2*F) : scalar b c d E F<0 := by
  let L := c+E
  let x := b-d
  have hLpos : 1≤L := by dsimp [L];omega
  have hd3 : 3≤d := by
    by_contra hn
    have hh := mul_nonneg (show 0≤2-d by omega) (show 0≤L by omega)
    change d*L=2*F at hWall
    nlinarith
  have hL3 : 3≤L := by
    by_contra hn
    have hh := mul_nonneg (show 0≤2-L by omega) (show 0≤d by omega)
    change d*L=2*F at hWall
    nlinarith
  have hF5 : 5≤F := by
    have hh := mul_nonneg (show 0≤d-3 by omega) (show 0≤L-3 by omega)
    change d*L=2*F at hWall
    nlinarith
  have hdRect := mul_nonneg (show 0≤d-3 by omega) (show 0≤F-1-d by omega)
  have hLRect := mul_nonneg (show 0≤L-3 by omega) (show 0≤F-1-L by dsimp [L];omega)
  have hdLRect := mul_nonneg (show 0≤d-3 by omega) (show 0≤L-3 by omega)
  have hSum : 3*(d+L)≤2*F+9 := by change d*L=2*F at hWall;nlinarith
  have hScale := mul_nonneg (show 0≤F+2 by omega) (show 0≤2*F+9-3*(d+L) by omega)
  have hSquares : 3*(d*d+L*L)≤2*F*F-5*F+36 := by nlinarith
  have hFc := mul_nonneg (show 0≤F by omega) (show 0≤c-1 by omega)
  have hX := mul_nonneg (show 0≤x by dsimp [x];omega)
    (show 0≤F*c-x-d-1 by dsimp [x];nlinarith)
  have hCE := mul_nonneg (show 0≤c-1 by omega) (show 0≤E-1 by omega)
  have hWallF : F*(d*(c+E))=2*F*F := by rw [hWall];ring
  have hRewrite : scalar b c d E F=
      1+d*d+L*L-c*E-F*F+x*x+d*x-F*c*x := by
    unfold scalar
    dsimp [x,L]
    nlinarith [hWallF]
  have hTop : scalar b c d E F≤d*d+L*L-c*E-F*F := by
    rw [hRewrite]
    dsimp [x] at hX
    dsimp [x]
    nlinarith
  have hNeg : -F*F-5*F+36<0 := by nlinarith
  nlinarith

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

private theorem seed_classes : ∀ s : Fin 3, ∀ i : Fin 6,
    ProperClassTable (ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1)) i →
    component (supportMask (ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1))) i=
      component (supportMask (ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1))) 4 := by decide

theorem proper_scalar (b c d E f : Int)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E)
    (p : CyclicOrder) (hp : ProperClass (ofSix 1 (-b) c d (-E) f) p) :
    orderMarkov (ofSix 1 (-b) c d (-E) f) p=
      1+b*b+c*c+d*d+E*E+f*f+c*E-b*d+b*c*f-d*E*f-b*c*d*E := by
  let s : Fin 3 := if f<0 then 0 else if f=0 then 1 else 2
  let seed := ofSix 1 (-1) 1 1 (-1) ((s.val:Int)-1)
  let Q := ofSix 1 (-b) c d (-E) f
  have hmask : supportMask Q=supportMask seed := by
    by_cases hn : f<0 <;> by_cases hz : f=0 <;>
      simp [Q,seed,s,supportMask,supportBit,ofSix,hn,hz,
        show b≠0 by omega,show c≠0 by omega,show d≠0 by omega,show E≠0 by omega]
  have hsign : ∀ i j,0<Q i j ↔ 0<seed i j := by
    intro i j
    by_cases hn : f<0 <;> by_cases hz : f=0 <;>
      rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;>
      simp [Q,seed,s,ofSix,hn,hz] <;> omega
  obtain ⟨i,hi⟩ := cyclic_order_exhaustive p
  have ht := (properClass_iff_table Q (ofSix_skew _ _ _ _ _ _) p i hi).mp hp
  have hs := (ChamberProperness.properClassTable_sign_iff Q seed hmask hsign i).mp ht
  have hcomp := seed_classes s i hs
  have hw : WiggleEquivalent Q p (order 4) := by
    apply (wiggle_iff_component Q (ofSix_skew _ _ _ _ _ _) p (order 4) i 4
      hi (fun _ _ _ => Iff.rfl)).mpr
    rwa [hmask]
  rw [ProperWiggleInvariants.markov_wiggle_invariant Q (ofSix_skew _ _ _ _ _ _) hw]
  have h0 : (order 4).toFun 0=0 := by decide
  have h1 : (order 4).toFun 1=3 := by decide
  have h2 : (order 4).toFun 2=1 := by decide
  have h3 : (order 4).toFun 3=2 := by decide
  simp only [orderMarkov,h0,h1,h2,h3,Q,ofSix]
  unfold Algebra.markov Algebra.squareSum Algebra.cycleTerms
  ring

theorem normalized_obstruction (b c d E F : Int)
    (hF : 2≤F) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E)
    (hbF : b≤F-1) (hdF : d≤F-1) (hL : c+E≤F)
    (hbd : d<b) (hbc : b*c≤2*F-1) (hCross : 2*F<b*c+d*E)
    (hTop : c+E=F ∨ d*(c+E)=2*F) :
    scalar b c d E F<0 ∨ F-1<2*abs (pf b c d E F) := by
  rcases hTop with hTop|hTop
  · exact Or.inr (incident_wall_large_pf b c d E F hF hb hc hd hE hbd hbc hCross hTop)
  · by_cases hIncident : c+E=F
    · exact Or.inr (incident_wall_large_pf b c d E F hF hb hc hd hE hbd hbc hCross hIncident)
    · exact Or.inl (opposite_wall_negative_scalar b c d E F hF hc hd hE hbF hdF
        (by omega) hbd hTop)

theorem normalized_MA_impossible (b c d E F : Int)
    (hF : 2≤F) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E)
    (hbF : b≤F-1) (hdF : d≤F-1) (hL : c+E≤F)
    (hbd : d<b) (hbc : b*c≤2*F-1) (hCross : 2*F<b*c+d*E)
    (hTop : c+E=F ∨ d*(c+E)=2*F)
    (p : CyclicOrder) (hp : TotalProper (root b c d E F) p)
    (hM : orderMarkov (root b c d E F) p≤F-1) :
    ¬MutationAcyclic (root b c d E F) := by
  intro hma
  have hm : orderMarkov (root b c d E F) p=scalar b c d E F := by
    have h := proper_scalar b c d E (F-b*c) hb hc hd hE p
      (totalProper_proper _ p hp)
    unfold root at ⊢
    rw [h]
    unfold scalar
    ring
  have hpf : matrixPfaffian (root b c d E F)=pf b c d E F := by
    simp only [matrixPfaffian,root,ofSix,pf]
    ring
  have hn := QuiverProofs.Rank4StructureRound2.SuperScalarPeak.MA_totalProper_pfaffian_bound
    EndpointFoundation.endpoint_bridge (root b c d E F) (ofSix_skew _ _ _ _ _ _) hma p hp
  rw [hm,hpf] at hn
  rw [hm] at hM
  rcases normalized_obstruction b c d E F hF hb hc hd hE hbF hdF hL hbd hbc hCross hTop
      with hs|hpf'
  · have hn0 := abs_nonneg (pf b c d E F)
    omega
  · omega

#print axioms incident_wall_large_pf
#print axioms opposite_wall_negative_scalar
#print axioms proper_scalar
#print axioms normalized_obstruction
#print axioms normalized_MA_impossible
end Rank4CoordinatorR2.UnitThreeScalar
