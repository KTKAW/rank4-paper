import QuiverProofs.ForkCertificates

/-! Small kernel-checked certificates for one-parameter integer polynomial
matrix identities and inequalities. Coefficient tests apply on the entire
nonnegative half-line; they do not evaluate a finite set of parameters. -/
namespace QuiverProofs.PolynomialCertificate
abbrev P := List Int

def eval : P → Int → Int
  | [], _ => 0
  | a::p, t => a+t*eval p t

def add : P → P → P
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def scale (a : Int) (p : P) : P := p.map (fun b => a*b)
def neg (p : P) : P := scale (-1) p
def sub (p q : P) : P := add p (neg q)
def mul : P → P → P
  | [], _ => []
  | a::p, q => add (scale a q) (0::mul p q)

theorem eval_add (p q : P) (t : Int) : eval (add p q) t=eval p t+eval q t := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih => cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,ih]; grind

theorem eval_scale (a : Int) (p : P) (t : Int) : eval (scale a p) t=a*eval p t := by
  induction p with
  | nil => simp [scale,eval]
  | cons b p ih => simp only [scale,List.map_cons,eval] at *; grind

theorem eval_neg (p : P) (t : Int) : eval (neg p) t = -eval p t := by
  simp [neg,eval_scale]
theorem eval_sub (p q : P) (t : Int) : eval (sub p q) t=eval p t-eval q t := by
  simp only [sub,eval_add,eval_neg]; omega
theorem eval_mul (p q : P) (t : Int) : eval (mul p q) t=eval p t*eval q t := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih => simp only [mul,eval_add,eval_scale,eval,ih]; grind

def nn (p : P) : Bool := p.all (fun a => decide (0≤a))
def zz (p : P) : Bool := p.all (fun a => decide (a=0))
def positive (p : P) : Bool := nn p && decide (0<p.headD 0)
def eqb (p q : P) : Bool := zz (sub p q)
def leb (p q : P) : Bool := nn (sub q p)
def ltb (p q : P) : Bool := positive (sub q p)

theorem nonnegative (p : P) (t : Int) (ht : 0≤t) (h : nn p=true) : 0≤eval p t := by
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
    have hp : 0≤a ∧ nn p=true := by simpa [nn] using h
    have hh := Int.mul_nonneg ht (ih hp.2)
    simp only [eval]; omega

theorem zero (p : P) (t : Int) (h : zz p=true) : eval p t=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hp : a=0 ∧ zz p=true := by simpa [zz] using h
    simp [eval,hp.1,ih hp.2]

theorem pos (p : P) (t : Int) (ht : 0≤t) (h : positive p=true) : 0<eval p t := by
  cases p with
  | nil => simp [positive] at h
  | cons a p =>
    have hp : 0≤a ∧ nn p=true ∧ 0<a := by simpa [positive,nn,and_assoc] using h
    have hh := Int.mul_nonneg ht (nonnegative p t ht hp.2.1)
    simp only [eval]; omega

theorem equal (p q : P) (t : Int) (h : eqb p q=true) : eval p t=eval q t := by
  have hh := zero (sub p q) t h
  rw [eval_sub] at hh; omega

theorem le (p q : P) (t : Int) (ht : 0≤t) (h : leb p q=true) : eval p t≤eval q t := by
  have hh := nonnegative (sub q p) t ht h
  rw [eval_sub] at hh; omega

theorem lt (p q : P) (t : Int) (ht : 0≤t) (h : ltb p q=true) : eval p t<eval q t := by
  have hh := pos (sub q p) t ht h
  rw [eval_sub] at hh; omega

def positivePart (p : P) : P := if nn p then p else []
def signed (p : P) : Bool := nn p || nn (neg p)

theorem eval_positivePart (p : P) (t : Int) (ht : 0≤t) (hs : signed p=true) :
    eval (positivePart p) t=max (eval p t) 0 := by
  by_cases hn : nn p=true
  · have hp := nonnegative p t ht hn
    simp [positivePart,hn]; omega
  · have hneg : nn (neg p)=true := by simpa [signed,hn] using hs
    have hp := nonnegative (neg p) t ht hneg
    rw [eval_neg] at hp
    simp [positivePart,hn,eval]; omega

theorem signed_neg (p : P) (h : signed p=true) : signed (neg p)=true := by
  have he : neg (neg p)=p := by
    simp [neg,scale,List.map_map,Function.comp_def]
  simp only [signed,he]
  simpa only [signed,Bool.or_comm] using h

def pcorr (p q : P) : P := sub (mul (positivePart p) (positivePart q))
  (mul (positivePart (neg p)) (positivePart (neg q)))

theorem eval_pcorr (p q : P) (t : Int) (ht : 0≤t)
    (hp : signed p=true) (hq : signed q=true) :
    eval (pcorr p q) t=correction (eval p t) (eval q t) := by
  simp only [pcorr,eval_sub,eval_mul,eval_positivePart p t ht hp,
    eval_positivePart q t ht hq,eval_positivePart (neg p) t ht (signed_neg p hp),
    eval_positivePart (neg q) t ht (signed_neg q hq),eval_neg,correction]

abbrev PMatrix := Fin 4 → Fin 4 → P
def matrix (B : PMatrix) (t : Int) : Matrix 4 := fun i j => eval (B i j) t
def six (a b c d e f : P) : PMatrix := fun i j =>
  match i.val,j.val with
  | 0,1 => a | 0,2 => b | 0,3 => c | 1,2 => d | 1,3 => e | 2,3 => f
  | 1,0 => neg a | 2,0 => neg b | 3,0 => neg c | 2,1 => neg d
  | 3,1 => neg e | 3,2 => neg f | _,_ => []

theorem matrix_six (a b c d e f : P) (t : Int) : matrix (six a b c d e f) t=
    ofSix (eval a t) (eval b t) (eval c t) (eval d t) (eval e t) (eval f t) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [matrix,six,ofSix,eval_neg,eval]

def pmutate (B : PMatrix) (k : Fin 4) : PMatrix := fun i j =>
  if i=k ∨ j=k then neg (B i j) else add (B i j) (pcorr (B i k) (B k j))

theorem matrix_mutate (B : PMatrix) (k : Fin 4) (t : Int) (ht : 0≤t)
    (hs : ∀ i j, signed (B i j)=true) :
    matrix (pmutate B k) t=mutate (matrix B t) k := by
  funext i j
  by_cases h : i=k ∨ j=k
  · simp [matrix,pmutate,mutate,h,eval_neg]
  · simp only [matrix,pmutate,mutate,h,↓reduceIte,eval_add,
      eval_pcorr _ _ t ht (hs i k) (hs k j)]

def prelabel (B : PMatrix) (p : Relabeling 4) : PMatrix := fun i j => B (p.toFun i) (p.toFun j)
def preverse (B : PMatrix) : PMatrix := fun i j => neg (B i j)

theorem matrix_relabel (B : PMatrix) (p : Relabeling 4) (t : Int) :
    matrix (prelabel B p) t=relabel (matrix B t) p := rfl

theorem matrix_reverse (B : PMatrix) (t : Int) :
    matrix (preverse B) t=reverse (matrix B t) := by
  funext i j; exact eval_neg _ _

theorem matrix_equal (B C : PMatrix) (t : Int) (h : ∀ i j, eqb (B i j) (C i j)=true) :
    matrix B t=matrix C t := by funext i j; exact equal _ _ _ (h i j)

theorem mutation_equal (B C : PMatrix) (k : Fin 4) (t : Int) (ht : 0≤t)
    (hs : ∀ i j, signed (B i j)=true)
    (he : ∀ i j, eqb (pmutate B k i j) (C i j)=true) :
    mutate (matrix B t) k=matrix C t := by
  rw [←matrix_mutate B k t ht hs]
  exact matrix_equal _ _ _ he

end QuiverProofs.PolynomialCertificate
