import Rank4Round2.MultiPolynomialCertificate
import QuiverProofs.GenericRegionAdapter
import QuiverProofs.UnitRegionRules
import QuiverProofs.PDRegionRules

namespace QuiverProofs.MultiRegionInterfaces
open MultiPolynomialCertificate RecursiveRegions Forks Regions
abbrev Region := (GenericRegionAdapter.Seed ⊕ UnitRegionData.Region) ⊕ PDRegionRules.Seed
def data : RegionData Region :=
  (GenericRegionAdapter.data.sum UnitRegionData.data).sum PDRegionRules.data
def rules : RegionRules data :=
  (GenericRegionAdapter.rules.sum UnitRegionRules.rules).sum PDRegionRules.rules

def generic (m a b c : P) (i : Fin 3) : PMatrix := match i.val with
  | 0 => six (const (-1)) (neg m) a (const (-1)) b (neg c)
  | 1 => six (const 1) m (neg a) (const (-1)) (add a b) (sub (mul m a) c)
  | _ => six (const (-1)) m b (const 1) (neg (add a b)) (sub (add (mul (add m (const 1)) a) b) c)

theorem generic_eval (m a b c : P) (i : Fin 3) (t : Fin 3 → Int) :
    matrix (generic m a b c i) t=GenericStrip.phase
      (eval m t) (eval a t) (eval b t) (eval c t) (Fin.castLE (by decide) i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with rfl|rfl|rfl <;>
    simp only [generic,matrix_six,eval_add,eval_mul,eval_sub,eval_neg,eval_const,
      GenericStrip.phase,GenericStrip.root,GenericStrip.phaseP,GenericStrip.phaseQ,
      GenericStrip.nextB,GenericStrip.nextC] <;> congr 1 <;> grind

def genericOK (m a b c : P) : Bool := leb (const 2) m && ltb m b && ltb b c && ltb c a

theorem generic_domain (m a b c : P) (t : Fin 3 → Int) (ht : ∀ i, 0≤t i)
    (h : genericOK m a b c=true) : GenericStrip.Domain (eval m t) (eval a t) (eval b t) (eval c t) := by
  have hh : ((leb (const 2) m=true ∧ ltb m b=true) ∧ ltb b c=true) ∧ ltb c a=true := by
    simpa only [genericOK,Bool.and_eq_true] using h
  exact ⟨by simpa [eval_const] using le (const 2) m t ht hh.1.1.1,
    lt m b t ht hh.1.1.2,lt b c t ht hh.1.2,lt c a t ht hh.2⟩

def zero (x u v w : P) (i : Fin 2) : PMatrix :=
  if i=0 then six (const 0) (neg u) (const 1) v (neg x) w
  else six (const 0) u (const (-1)) v (neg x) (add u w)

theorem zero_eval (x u v w : P) (i : Fin 2) (t : Fin 3 → Int) :
    matrix (zero x u v w i) t=UnitZeroStrip.node
      (eval x t) (eval u t) (eval v t) (eval w t) (Fin.castLE (by decide) i) := by
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl|rfl <;>
    simp [zero,matrix_six,eval_add,eval_neg,eval_const,UnitZeroStrip.node]

def zeroOK (x u v w : P) : Bool := leb (const 2) x && leb (const 2) u && ltb x v && ltb v w

theorem zero_domain (x u v w : P) (t : Fin 3 → Int) (ht : ∀ i, 0≤t i)
    (h : zeroOK x u v w=true) : UnitZeroStrip.Domain (eval x t) (eval u t) (eval v t) (eval w t) := by
  have hh : ((leb (const 2) x=true ∧ leb (const 2) u=true) ∧ ltb x v=true) ∧ ltb v w=true := by
    simpa only [zeroOK,Bool.and_eq_true] using h
  exact ⟨by simpa [eval_const] using le (const 2) x t ht hh.1.1.1,
    by simpa [eval_const] using le (const 2) u t ht hh.1.1.2,
    lt x v t ht hh.1.2,lt v w t ht hh.2⟩

def pendant (c d x y : P) (i : Fin 2) : PMatrix :=
  six (const 0) (const 0) (if i=0 then c else neg c) d (neg x) y

theorem pendant_eval (c d x y : P) (i : Fin 2) (t : Fin 3 → Int) :
    matrix (pendant c d x y i) t=PendantSquare.state
      (eval c t) (eval d t) (eval x t) (eval y t) (PDRegionRules.sign i) := by
  have hi : i=0 ∨ i=1 := by omega
  rcases hi with rfl|rfl <;>
    simp [pendant,matrix_six,eval_neg,eval_const,PendantSquare.state,PDRegionRules.sign]

def pendantOK (c d x y : P) : Bool :=
  leb (const 2) c && leb (const 2) d && leb (const 2) x && ltb d y && ltb x y

theorem pendant_domain (c d x y : P) (t : Fin 3 → Int) (ht : ∀ i, 0≤t i)
    (h : pendantOK c d x y=true) : PendantSquare.Domain (eval c t) (eval d t) (eval x t) (eval y t) := by
  have hh : (((leb (const 2) c=true ∧ leb (const 2) d=true) ∧ leb (const 2) x=true) ∧ ltb d y=true) ∧ ltb x y=true := by
    simpa only [pendantOK,Bool.and_eq_true] using h
  exact ⟨by simpa [eval_const] using le (const 2) c t ht hh.1.1.1.1,
    by simpa [eval_const] using le (const 2) d t ht hh.1.1.1.2,
    by simpa [eval_const] using le (const 2) x t ht hh.1.1.2,
    lt d y t ht hh.1.2,lt x y t ht hh.2⟩

def fork (a b c d e f : P) : PMatrix := six (neg a) b c (neg d) (neg e) f
def forkOK (a b c d e f : P) : Bool :=
  leb (const 2) a && leb (const 2) b && leb (const 2) c && ltb a d && ltb b d && ltb a e && ltb c e && leb (const 2) f

theorem fork_sound (a b c d e f : P) (t : Fin 3 → Int) (ht : ∀ i, 0≤t i)
    (h : forkOK a b c d e f=true) : IsFork (matrix (fork a b c d e f) t) 0 := by
  have hh : ((((((leb (const 2) a=true ∧ leb (const 2) b=true) ∧ leb (const 2) c=true) ∧ ltb a d=true) ∧
    ltb b d=true) ∧ ltb a e=true) ∧ ltb c e=true) ∧ leb (const 2) f=true := by
    simpa only [forkOK,Bool.and_eq_true] using h
  have hd : Forks.Domain (eval a t) (eval b t) (eval c t) (eval d t) (eval e t) (eval f t) :=
    ⟨by simpa [eval_const] using le (const 2) a t ht hh.1.1.1.1.1.1.1,
     by simpa [eval_const] using le (const 2) b t ht hh.1.1.1.1.1.1.2,
     by simpa [eval_const] using le (const 2) c t ht hh.1.1.1.1.1.2,
     lt a d t ht hh.1.1.1.1.2,lt b d t ht hh.1.1.1.2,
     lt a e t ht hh.1.1.2,lt c e t ht hh.1.2,
     by simpa [eval_const] using le (const 2) f t ht hh.2⟩
  simpa only [fork,matrix_six,eval_neg,Forks.template] using IsFork.basic _ _ _ _ _ _ hd

def root (a b c d e ep : P) : PMatrix := six a (neg d) (neg e) b c ep
def rootOK (a b c d e ep : P) : Bool :=
  leb (const 2) a && leb (const 2) d && leb (const 2) e && ltb a b && ltb d b && ltb a c && ltb e c &&
    (eqb ep (const 0) || eqb ep (const 1))

theorem root_sound (a b c d e ep : P) (t : Fin 3 → Int) (ht : ∀ i, 0≤t i)
    (h : rootOK a b c d e ep=true) : IsRoot (matrix (root a b c d e ep) t) 0 := by
  have hh : ((((((leb (const 2) a=true ∧ leb (const 2) d=true) ∧ leb (const 2) e=true) ∧ ltb a b=true) ∧
    ltb d b=true) ∧ ltb a c=true) ∧ ltb e c=true) ∧ (eqb ep (const 0)=true ∨ eqb ep (const 1)=true) := by
    simpa only [rootOK,Bool.and_eq_true,Bool.or_eq_true] using h
  have hd : Regions.Domain (eval a t) (eval b t) (eval c t) (eval d t) (eval e t) :=
    ⟨by simpa [eval_const] using le (const 2) a t ht hh.1.1.1.1.1.1.1,
     by simpa [eval_const] using le (const 2) d t ht hh.1.1.1.1.1.1.2,
     by simpa [eval_const] using le (const 2) e t ht hh.1.1.1.1.1.2,
     lt a b t ht hh.1.1.1.1.2,lt d b t ht hh.1.1.1.2,
     lt a c t ht hh.1.1.2,lt e c t ht hh.1.2⟩
  have he : eval ep t=0 ∨ eval ep t=1 := by
    rcases hh.2 with hz|ho
    · exact Or.inl (by simpa only [eval_const] using equal ep (const 0) t hz)
    · exact Or.inr (by simpa [eval_const] using equal ep (const 1) t ho)
  simpa only [root,matrix_six,eval_neg,Regions.root] using IsRoot.basic _ _ _ _ _ _ hd he

end QuiverProofs.MultiRegionInterfaces
