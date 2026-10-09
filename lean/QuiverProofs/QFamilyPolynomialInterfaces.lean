import QuiverProofs.PolynomialCertificate
import QuiverProofs.GenericRegionAdapter
import QuiverProofs.UnitRegionRules
import QuiverProofs.PDRegionRules

namespace QuiverProofs.QFamilyPolynomialInterfaces
open PolynomialCertificate RecursiveRegions Forks Regions
abbrev Region := (GenericRegionAdapter.Seed ⊕ UnitRegionData.Region) ⊕ PDRegionRules.Seed
def data : RegionData Region :=
  (GenericRegionAdapter.data.sum UnitRegionData.data).sum PDRegionRules.data
def rules : RegionRules data :=
  (GenericRegionAdapter.rules.sum UnitRegionRules.rules).sum PDRegionRules.rules

def generic (m a b c : P) (i : Fin 3) : PMatrix := match i.val with
  | 0 => six [-1] (neg m) a [-1] b (neg c)
  | 1 => six [1] m (neg a) [-1] (add a b) (sub (mul m a) c)
  | _ => six [-1] m b [1] (neg (add a b)) (sub (add (mul (add m [1]) a) b) c)

theorem generic_eval (m a b c : P) (i : Fin 3) (t : Int) :
    matrix (generic m a b c i) t=GenericStrip.phase
      (eval m t) (eval a t) (eval b t) (eval c t) (Fin.castLE (by decide) i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with rfl|rfl|rfl <;>
    simp only [generic,matrix_six,eval_add,eval_mul,eval_sub,eval_neg,eval,
      GenericStrip.phase,GenericStrip.root,GenericStrip.phaseP,GenericStrip.phaseQ,
      GenericStrip.nextB,GenericStrip.nextC] <;> congr 1 <;> grind

def genericOK (m a b c : P) : Bool := leb [2] m && ltb m b && ltb b c && ltb c a

theorem generic_domain (m a b c : P) (t : Int) (ht : 0≤t)
    (h : genericOK m a b c=true) : GenericStrip.Domain (eval m t) (eval a t) (eval b t) (eval c t) := by
  have hh : ((leb [2] m=true ∧ ltb m b=true) ∧ ltb b c=true) ∧ ltb c a=true := by
    simpa only [genericOK,Bool.and_eq_true] using h
  exact ⟨by simpa [eval] using le [2] m t ht hh.1.1.1,
    lt m b t ht hh.1.1.2,lt b c t ht hh.1.2,lt c a t ht hh.2⟩

def zero (x u v w : P) (i : Fin 2) : PMatrix :=
  if i=0 then six [] (neg u) [1] v (neg x) w
  else six [] u [-1] v (neg x) (add u w)

theorem zero_eval (x u v w : P) (i : Fin 2) (t : Int) :
    matrix (zero x u v w i) t=UnitZeroStrip.node
      (eval x t) (eval u t) (eval v t) (eval w t) (Fin.castLE (by decide) i) := by
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl|rfl <;>
    simp [zero,matrix_six,eval_add,eval_neg,eval,UnitZeroStrip.node]

def zeroOK (x u v w : P) : Bool := leb [2] x && leb [2] u && ltb x v && ltb v w

theorem zero_domain (x u v w : P) (t : Int) (ht : 0≤t)
    (h : zeroOK x u v w=true) : UnitZeroStrip.Domain (eval x t) (eval u t) (eval v t) (eval w t) := by
  have hh : ((leb [2] x=true ∧ leb [2] u=true) ∧ ltb x v=true) ∧ ltb v w=true := by
    simpa only [zeroOK,Bool.and_eq_true] using h
  exact ⟨by simpa [eval] using le [2] x t ht hh.1.1.1,
    by simpa [eval] using le [2] u t ht hh.1.1.2,
    lt x v t ht hh.1.2,lt v w t ht hh.2⟩

def pendant (c d x y : P) (i : Fin 2) : PMatrix :=
  six [] [] (if i=0 then c else neg c) d (neg x) y

theorem pendant_eval (c d x y : P) (i : Fin 2) (t : Int) :
    matrix (pendant c d x y i) t=PendantSquare.state
      (eval c t) (eval d t) (eval x t) (eval y t) (PDRegionRules.sign i) := by
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl|rfl <;>
    simp [pendant,matrix_six,eval_neg,eval,PendantSquare.state,PDRegionRules.sign]

def pendantOK (c d x y : P) : Bool :=
  leb [2] c && leb [2] d && leb [2] x && ltb d y && ltb x y

theorem pendant_domain (c d x y : P) (t : Int) (ht : 0≤t)
    (h : pendantOK c d x y=true) : PendantSquare.Domain (eval c t) (eval d t) (eval x t) (eval y t) := by
  have hh : (((leb [2] c=true ∧ leb [2] d=true) ∧ leb [2] x=true) ∧ ltb d y=true) ∧ ltb x y=true := by
    simpa only [pendantOK,Bool.and_eq_true] using h
  exact ⟨by simpa [eval] using le [2] c t ht hh.1.1.1.1,
    by simpa [eval] using le [2] d t ht hh.1.1.1.2,
    by simpa [eval] using le [2] x t ht hh.1.1.2,
    lt d y t ht hh.1.2,lt x y t ht hh.2⟩

def fork (a b c d e f : P) : PMatrix := six (neg a) b c (neg d) (neg e) f
def forkOK (a b c d e f : P) : Bool :=
  leb [2] a && leb [2] b && leb [2] c && ltb a d && ltb b d && ltb a e && ltb c e && leb [2] f

theorem fork_sound (a b c d e f : P) (t : Int) (ht : 0≤t)
    (h : forkOK a b c d e f=true) : IsFork (matrix (fork a b c d e f) t) 0 := by
  have hh : ((((((leb [2] a=true ∧ leb [2] b=true) ∧ leb [2] c=true) ∧ ltb a d=true) ∧
    ltb b d=true) ∧ ltb a e=true) ∧ ltb c e=true) ∧ leb [2] f=true := by
    simpa only [forkOK,Bool.and_eq_true] using h
  have hd : Forks.Domain (eval a t) (eval b t) (eval c t) (eval d t) (eval e t) (eval f t) :=
    ⟨by simpa [eval] using le [2] a t ht hh.1.1.1.1.1.1.1,
     by simpa [eval] using le [2] b t ht hh.1.1.1.1.1.1.2,
     by simpa [eval] using le [2] c t ht hh.1.1.1.1.1.2,
     lt a d t ht hh.1.1.1.1.2,lt b d t ht hh.1.1.1.2,
     lt a e t ht hh.1.1.2,lt c e t ht hh.1.2,
     by simpa [eval] using le [2] f t ht hh.2⟩
  simpa only [fork,matrix_six,eval_neg,Forks.template] using IsFork.basic _ _ _ _ _ _ hd

def root (a b c d e ep : P) : PMatrix := six a (neg d) (neg e) b c ep
def rootOK (a b c d e ep : P) : Bool :=
  leb [2] a && leb [2] d && leb [2] e && ltb a b && ltb d b && ltb a c && ltb e c &&
    (eqb ep [] || eqb ep [1])

theorem root_sound (a b c d e ep : P) (t : Int) (ht : 0≤t)
    (h : rootOK a b c d e ep=true) : IsRoot (matrix (root a b c d e ep) t) 0 := by
  have hh : ((((((leb [2] a=true ∧ leb [2] d=true) ∧ leb [2] e=true) ∧ ltb a b=true) ∧
    ltb d b=true) ∧ ltb a c=true) ∧ ltb e c=true) ∧ (eqb ep []=true ∨ eqb ep [1]=true) := by
    simpa only [rootOK,Bool.and_eq_true,Bool.or_eq_true] using h
  have hd : Regions.Domain (eval a t) (eval b t) (eval c t) (eval d t) (eval e t) :=
    ⟨by simpa [eval] using le [2] a t ht hh.1.1.1.1.1.1.1,
     by simpa [eval] using le [2] d t ht hh.1.1.1.1.1.1.2,
     by simpa [eval] using le [2] e t ht hh.1.1.1.1.1.2,
     lt a b t ht hh.1.1.1.1.2,lt d b t ht hh.1.1.1.2,
     lt a c t ht hh.1.1.2,lt e c t ht hh.1.2⟩
  have he : eval ep t=0 ∨ eval ep t=1 := by
    rcases hh.2 with hz|ho
    · exact Or.inl (equal ep [] t hz)
    · exact Or.inr (by simpa [eval] using equal ep [1] t ho)
  simpa only [root,matrix_six,eval_neg,Regions.root] using IsRoot.basic _ _ _ _ _ _ hd he

end QuiverProofs.QFamilyPolynomialInterfaces
