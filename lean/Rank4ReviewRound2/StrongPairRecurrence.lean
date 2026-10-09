import Rank4ReviewRound2.StrongPairColumn

/-! Exact frozen-column recurrence when the two pivot roles are swapped
following each mutation. Positive columns grow at least linearly; a negative
coefficient enters that growing cone within three steps. These are local
integer statements, not MA or opposite-edge coverage claims. -/
namespace Rank4ReviewRound2.StrongPairRecurrence
open QuiverProofs

def columnStep (a : Int) (p : Int × Int) : Int × Int :=
  (-p.2,p.1+correction a p.2)

def orbit (a : Int) (p : Int × Int) : Nat → Int × Int
  | 0 => p
  | n+1 => columnStep a (orbit a p n)

def Growing (p : Int × Int) : Prop := p.1≤0 ∧ 0≤p.2 ∧ 1≤p.1+p.2

theorem step_formula (a b d : Int) (ha : 0≤a) :
    columnStep a (b,d)=(-d,b+a*max d 0) := by
  simp only [columnStep,correction,max_eq_left ha,
    max_eq_right (show -a≤0 by omega)]
  ring_nf

theorem growing_step (a : Int) (ha : 2≤a) (p : Int × Int)
    (hg : Growing p) : Growing (columnStep a p) ∧ p.2+1≤(columnStep a p).2 := by
  rcases p with ⟨b,d⟩
  rcases hg with ⟨hb,hd,hbd⟩
  rw [step_formula a b d (by omega),max_eq_left hd]
  have hp := mul_nonneg (show 0≤a-2 by omega) hd
  unfold Growing
  simp only [Prod.fst,Prod.snd]
  constructor
  · exact ⟨by omega,by nlinarith,by nlinarith⟩
  · nlinarith

theorem growing_orbit (a : Int) (ha : 2≤a) (p : Int × Int) (hg : Growing p) (n : Nat) :
    Growing (orbit a p n) ∧ p.2+(n:Int)≤(orbit a p n).2 := by
  induction n with
  | zero => exact ⟨hg,by simp [orbit]⟩
  | succ n ih =>
    have hs := growing_step a ha (orbit a p n) ih.1
    refine ⟨hs.1,?_⟩
    change p.2+((n+1:Nat):Int)≤(columnStep a (orbit a p n)).2
    simp only [Nat.cast_add,Nat.cast_one]
    omega

theorem positive_seed_grows (a b d : Int) (ha : 2≤a) (hb : 1≤b) (hd : 0≤d) :
    Growing (columnStep a (b,d)) ∧ d+1≤(columnStep a (b,d)).2 := by
  rw [step_formula a b d (by omega),max_eq_left hd]
  unfold Growing
  simp only [Prod.fst,Prod.snd]
  have hp := mul_nonneg (show 0≤a-2 by omega) hd
  constructor
  · exact ⟨by omega,by nlinarith,by nlinarith⟩
  · nlinarith

theorem negative_enters_growth (a b d : Int) (ha : 2≤a) (hd : d<0) :
    Growing (orbit a (b,d) 3) := by
  have hfirst : orbit a (b,d) 1=(-d,b) := by
    simp only [orbit,step_formula a b d (by omega),max_eq_right (show d≤0 by omega)]
    simp
  by_cases hb : 0≤b
  · have hsecond : orbit a (b,d) 2=(-b,-d+a*b) := by
      change columnStep a (orbit a (b,d) 1)=_
      rw [hfirst,step_formula a (-d) b (by omega),max_eq_left hb]
    have hG : Growing (orbit a (b,d) 2) := by
      rw [hsecond]
      unfold Growing
      simp only [Prod.fst,Prod.snd]
      have hp := mul_nonneg (show 0≤a-2 by omega) hb
      exact ⟨by omega,by nlinarith,by nlinarith⟩
    exact (growing_step a ha _ hG).1
  · have hb' : b≤0 := by omega
    have hsecond : orbit a (b,d) 2=(-b,-d) := by
      change columnStep a (orbit a (b,d) 1)=_
      rw [hfirst,step_formula a (-d) b (by omega),max_eq_right hb']
      simp
    change Growing (columnStep a (orbit a (b,d) 2))
    rw [hsecond]
    exact (positive_seed_grows a (-b) (-d) ha (by omega) (by omega)).1

theorem actual_column_step (B : Matrix 4) (i j l : Fin 4)
    (hij : i≠j) (hil : i≠l) (hjl : j≠l) :
    (mutate B j j l,mutate B j i l)=columnStep (B i j) (B i l,B j l) := by
  simp only [columnStep,Prod.fst,Prod.snd,mutate,true_or,if_true,
    if_neg (show ¬(i=j ∨ l=j) by omega)]

#print axioms growing_orbit
#print axioms negative_enters_growth
#print axioms actual_column_step
end Rank4ReviewRound2.StrongPairRecurrence
