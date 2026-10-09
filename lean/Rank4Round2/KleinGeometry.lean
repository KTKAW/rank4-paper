import Rank4Round2.PeakAlgebra
import QuiverProofs.Forks
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Symbolic geometry of the six-parameter cross-guarded deep region.
The four cross guards are explicit sufficient hypotheses, not MA necessary
conditions. Every return and fork is checked in the original matrix semantics.
-/
namespace Rank4Round2.KleinRegion
open QuiverProofs Rank4Round2 Forks
set_option maxHeartbeats 4000000

structure Parameters where
  a : Int
  c : Int
  d : Int
  h : Int
  E : Int
  B : Int

def b (s : Parameters) := s.B-s.a*s.d
def e (s : Parameters) := s.E-s.a*s.c
def S (s : Parameters) := s.d*s.E-s.h
def T (s : Parameters) := s.c*s.B-s.h
def f (s : Parameters) := b s*s.c+s.d*s.E-s.h
def Domain (s : Parameters) : Prop :=
  2≤s.a ∧ 2≤s.c ∧ 2≤s.d ∧ 2≤s.h ∧
  2≤e s ∧ 2≤s.E-s.d*s.h ∧ 2≤b s ∧ 2≤s.B-s.c*s.h

def tau (s : Parameters) : Parameters := ⟨s.d,s.h,s.a,s.c,s.E,s.B⟩
def sigma (s : Parameters) : Parameters := ⟨s.c,s.a,s.h,s.d,s.E,s.B⟩

theorem tau_domain (s : Parameters) (hs : Domain s) : Domain (tau s) := by
  simp only [Domain,tau,b,e,Int.mul_comm] at *
  tauto
theorem sigma_domain (s : Parameters) (hs : Domain s) : Domain (sigma s) := by
  simp only [Domain,sigma,b,e,Int.mul_comm] at *
  tauto
theorem tau_involutive (s : Parameters) : tau (tau s)=s := by cases s; rfl
theorem sigma_involutive (s : Parameters) : sigma (sigma s)=s := by cases s; rfl
theorem tau_sigma (s : Parameters) : tau (sigma s)=sigma (tau s) := rfl

theorem f_rewritten (s : Parameters) : f s=T s+s.d*e s := by
  simp only [f,T,b,e]
  ring

theorem bounds (s : Parameters) (hs : Domain s) :
    2≤s.a ∧ 2≤s.c ∧ 2≤s.d ∧ 2≤s.h ∧ 2≤b s ∧ 2≤e s ∧
    s.a<s.E ∧ s.c<s.E ∧ s.d<s.E ∧ s.h<s.E ∧
    s.a<s.B ∧ s.c<s.B ∧ s.d<s.B ∧ s.h<s.B ∧
    s.E<S s ∧ s.d<S s ∧ s.B<T s ∧ s.c<T s ∧
    s.E<f s ∧ s.B<f s := by
  obtain ⟨ha,hc,hd,hh,he,he',hb,hb'⟩ := hs
  have hac_a := Int.mul_le_mul_of_nonneg_left hc (show 0≤s.a by omega)
  have hac_c := Int.mul_le_mul_of_nonneg_right ha (show 0≤s.c by omega)
  have hdh_d := Int.mul_le_mul_of_nonneg_left hh (show 0≤s.d by omega)
  have hdh_h := Int.mul_le_mul_of_nonneg_right hd (show 0≤s.h by omega)
  have had_a := Int.mul_le_mul_of_nonneg_left hd (show 0≤s.a by omega)
  have had_d := Int.mul_le_mul_of_nonneg_right ha (show 0≤s.d by omega)
  have hch_c := Int.mul_le_mul_of_nonneg_left hh (show 0≤s.c by omega)
  have hch_h := Int.mul_le_mul_of_nonneg_right hc (show 0≤s.h by omega)
  have haE : s.a<s.E := by unfold e at he; omega
  have hcE : s.c<s.E := by unfold e at he; omega
  have hdE : s.d<s.E := by omega
  have hhE : s.h<s.E := by omega
  have haB : s.a<s.B := by unfold b at hb; omega
  have hdB : s.d<s.B := by unfold b at hb; omega
  have hcB : s.c<s.B := by omega
  have hhB : s.h<s.B := by omega
  have hS := product_sub_dominates s.d s.E s.h hd hdE hhE
  have hT := product_sub_dominates s.c s.B s.h hc hcB hhB
  have hbc := mul_nonneg (show 0≤b s by omega) (show 0≤s.c by omega)
  have hde := mul_nonneg (show 0≤s.d by omega) (show 0≤e s by omega)
  have hEf : s.E<f s := by dsimp only [f,S] at *; omega
  have hBf : s.B<f s := by rw [f_rewritten]; dsimp only [T] at *; omega
  exact ⟨ha,hc,hd,hh,hb,he,haE,hcE,hdE,hhE,haB,hcB,hdB,hhB,
    hS.2,hS.1,hT.2,hT.1,hEf,hBf⟩

def node (s : Parameters) (i : Fin 3) : Matrix 4 := match i.val with
  | 0 => ofSix s.a (b s) (-s.c) s.d (-e s) (f s)
  | 1 => ofSix (-s.a) (-b s) s.c s.d (-s.E) (S s)
  | _ => ofSix (-s.a) s.B (-s.c) (-s.d) (e s) (T s)

private theorem four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

def swap02 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>2 | 1=>1 | 2=>0 | _=>3,
   fun i => match i.val with | 0=>2 | 1=>1 | 2=>0 | _=>3,by decide,by decide⟩
def swap13 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>0 | 1=>3 | 2=>2 | _=>1,
   fun i => match i.val with | 0=>0 | 1=>3 | 2=>2 | _=>1,by decide,by decide⟩
def frame2301 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>2 | 1=>3 | 2=>0 | _=>1,
   fun i => match i.val with | 0=>2 | 1=>3 | 2=>0 | _=>1,by decide,by decide⟩
def frame3210 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>3 | 1=>2 | 2=>1 | _=>0,
   fun i => match i.val with | 0=>3 | 1=>2 | 2=>1 | _=>0,by decide,by decide⟩
def frame2130 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>2 | 1=>1 | 2=>3 | _=>0,
   fun i => match i.val with | 0=>3 | 1=>1 | 2=>0 | _=>2,by decide,by decide⟩
def frame3120 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>3 | 1=>1 | 2=>2 | _=>0,
   fun i => match i.val with | 0=>3 | 1=>1 | 2=>2 | _=>0,by decide,by decide⟩
def frame2031 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>2 | 1=>0 | 2=>3 | _=>1,
   fun i => match i.val with | 0=>1 | 1=>3 | 2=>0 | _=>2,by decide,by decide⟩
def frame3021 : Relabeling 4 :=
  ⟨fun i => match i.val with | 0=>3 | 1=>0 | 2=>2 | _=>1,
   fun i => match i.val with | 0=>1 | 1=>3 | 2=>2 | _=>0,by decide,by decide⟩

theorem node_zero (s : Parameters) (hs : Domain s) : mutate (node s 0) 0=node s 1 := by
  have hb := bounds s hs
  change mutate (positivePeak s.a (b s) s.c s.d (e s) (f s)) 0=_
  rw [positivePeak_zero _ _ _ _ _ _ (by omega) (by omega) (by omega)]
  unfold node f S e
  congr 1 <;> ring

theorem node_one (s : Parameters) (hs : Domain s) : mutate (node s 0) 1=node s 2 := by
  have hb := bounds s hs
  change mutate (positivePeak s.a (b s) s.c s.d (e s) (f s)) 1=_
  rw [positivePeak_one _ _ _ _ _ _ (by omega) (by omega) (by omega)]
  unfold node f T b e
  congr 1 <;> ring

theorem tau_return (s : Parameters) (hs : Domain s) :
    mutate (node s 1) 1=reverse (relabel (node (tau s) 1) swap02) := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,tau,b,S,mutate,correction,ofSix,reverse,relabel,swap02] <;> grind

theorem sigma_return (s : Parameters) (hs : Domain s) :
    mutate (node s 2) 0=reverse (relabel (node (sigma s) 2) swap13) := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,sigma,e,T,mutate,correction,ofSix,reverse,relabel,swap13] <;> grind

theorem shape02 (s : Parameters) (hs : Domain s) :
    relabel (mutate (node s 0) 2) frame2301=
      template (f s) (b s) s.d (b s*f s-s.c) (s.d*f s-e s) s.a := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,template,mutate,correction,ofSix,relabel,frame2301] <;> grind

theorem shape03 (s : Parameters) (hs : Domain s) :
    relabel (reverse (mutate (node s 0) 3)) frame3210=
      template (f s) (e s) s.c (e s*f s-s.d) (s.c*f s-b s) s.a := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,template,mutate,correction,ofSix,relabel,reverse,frame3210] <;> grind

theorem shape12 (s : Parameters) (hs : Domain s) :
    relabel (reverse (mutate (node s 1) 2)) frame2130=
      template s.d (S s) (b s) (s.d*S s-s.E) (s.a+b s*s.d) s.c := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,template,mutate,correction,ofSix,relabel,reverse,frame2130] <;> grind

theorem shape13 (s : Parameters) (hs : Domain s) :
    relabel (mutate (node s 1) 3) frame3120=
      template s.E (S s) s.c (s.E*S s-s.d) (s.c*s.E-s.a) (b s) := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,template,mutate,correction,ofSix,relabel,frame3120] <;> grind

theorem shape22 (s : Parameters) (hs : Domain s) :
    relabel (reverse (mutate (node s 2) 2)) frame2031=
      template s.B (T s) s.d (s.B*T s-s.c) (s.d*s.B-s.a) (e s) := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,template,mutate,correction,ofSix,relabel,reverse,frame2031] <;> grind

theorem shape23 (s : Parameters) (hs : Domain s) :
    relabel (mutate (node s 2) 3) frame3021=
      template s.c (T s) (e s) (s.c*T s-s.B) (s.a+s.c*e s) s.d := by
  have hb := bounds s hs
  funext i j
  rcases four i with rfl|rfl|rfl|rfl <;>
    rcases four j with rfl|rfl|rfl|rfl <;>
    simp [node,template,mutate,correction,ofSix,relabel,frame3021] <;> grind

#print axioms bounds
#print axioms tau_return
#print axioms sigma_return
#print axioms shape02
#print axioms shape23
end Rank4Round2.KleinRegion
