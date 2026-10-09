import QuiverProofs.ForkCertificates

/-! Sparse three-variable integer polynomial certificates. Boolean tests
inspect normalized coefficients; soundness holds on the whole nonnegative
orthant and uses no sampled parameter evaluations. -/
namespace QuiverProofs.MultiPolynomialCertificate
abbrev Exponent := Nat × Nat × Nat
abbrev Term := Int × Exponent
abbrev P := List Term
abbrev Point := Fin 3 → Int

def weight (e : Exponent) (t : Point) : Int := t 0 ^ e.1 * t 1 ^ e.2.1 * t 2 ^ e.2.2

def eval : P → Point → Int
  | [], _ => 0
  | (a,e)::p, t => a*weight e t + eval p t

def monomial (a : Int) (i j k : Nat) : P := [(a,i,j,k)]
def const (a : Int) : P := monomial a 0 0 0
def «variable» (i : Fin 3) : P :=
  if i=0 then monomial 1 1 0 0 else if i=1 then monomial 1 0 1 0 else monomial 1 0 0 1

def add (p q : P) : P := p ++ q
def neg (p : P) : P := p.map (fun a => (-a.1,a.2))
def sub (p q : P) : P := add p (neg q)
def exponentAdd (e f : Exponent) : Exponent := (e.1+f.1,e.2.1+f.2.1,e.2.2+f.2.2)
def scaleMonomial (a : Int) (e : Exponent) (p : P) : P :=
  p.map (fun b => (a*b.1,exponentAdd e b.2))
def mul : P → P → P
  | [], _ => []
  | (a,e)::p, q => add (scaleMonomial a e q) (mul p q)

theorem eval_const (a : Int) (t : Point) : eval (const a) t = a := by
  simp [const,monomial,eval,weight]

theorem eval_variable (i : Fin 3) (t : Point) : eval («variable» i) t = t i := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with rfl|rfl|rfl <;> simp [«variable»,monomial,eval,weight,Int.pow_succ]

theorem weight_add (e f : Exponent) (t : Point) :
    weight (exponentAdd e f) t = weight e t * weight f t := by
  simp only [weight,exponentAdd,Int.pow_add]
  grind

theorem weight_nonnegative (e : Exponent) (t : Point) (ht : ∀ i, 0 ≤ t i) :
    0 ≤ weight e t :=
  Int.mul_nonneg (Int.mul_nonneg (Int.pow_nonneg (ht 0)) (Int.pow_nonneg (ht 1)))
    (Int.pow_nonneg (ht 2))

theorem eval_add (p q : P) (t : Point) : eval (add p q) t = eval p t + eval q t := by
  induction p with
  | nil => simp [add,eval]
  | cons a p ih => rcases a with ⟨a,e⟩; simp only [add,List.cons_append,eval] at *; omega

theorem eval_neg (p : P) (t : Point) : eval (neg p) t = -eval p t := by
  induction p with
  | nil => simp [neg,eval]
  | cons a p ih => rcases a with ⟨a,e⟩; simp only [neg,List.map_cons,eval] at *; grind

theorem eval_sub (p q : P) (t : Point) : eval (sub p q) t = eval p t-eval q t := by
  simp only [sub,eval_add,eval_neg]; omega

theorem eval_scaleMonomial (a : Int) (e : Exponent) (p : P) (t : Point) :
    eval (scaleMonomial a e p) t = a*weight e t*eval p t := by
  induction p with
  | nil => simp [scaleMonomial,eval]
  | cons b p ih =>
    rcases b with ⟨b,f⟩
    simp only [scaleMonomial,List.map_cons,eval,weight_add] at *
    grind

theorem eval_mul (p q : P) (t : Point) : eval (mul p q) t = eval p t*eval q t := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih =>
    rcases a with ⟨a,e⟩
    simp only [mul,eval_add,eval_scaleMonomial,eval,ih]
    grind

/-- Merge a monomial into a sparse polynomial; retaining zero coefficients
keeps this operation total and its preservation proof elementary. -/
def insertTerm (a : Int) (e : Exponent) : P → P
  | [] => [(a,e)]
  | (b,f)::p => if e=f then (a+b,f)::p else (b,f)::insertTerm a e p

def normalize : P → P
  | [] => []
  | (a,e)::p => insertTerm a e (normalize p)

theorem eval_insertTerm (a : Int) (e : Exponent) (p : P) (t : Point) :
    eval (insertTerm a e p) t = a*weight e t + eval p t := by
  induction p with
  | nil => simp [insertTerm,eval]
  | cons b p ih =>
    rcases b with ⟨b,f⟩
    by_cases he : e=f
    · subst e
      rw [insertTerm,if_pos rfl]
      simp only [eval]
      grind
    · simp only [insertTerm,if_neg he,eval,ih]; omega

theorem eval_normalize (p : P) (t : Point) : eval (normalize p) t = eval p t := by
  induction p with
  | nil => rfl
  | cons a p ih => rcases a with ⟨a,e⟩; simp only [normalize,eval_insertTerm,ih,eval]

def rawNN (p : P) : Bool := p.all (fun a => decide (0 ≤ a.1))
def rawZZ (p : P) : Bool := p.all (fun a => decide (a.1=0))
def rawPositive (p : P) : Bool := rawNN p && p.any (fun a => decide (a.2=(0,0,0) ∧ 0<a.1))
def nn (p : P) : Bool := rawNN (normalize p)
def zz (p : P) : Bool := rawZZ (normalize p)
def positive (p : P) : Bool := rawPositive (normalize p)
def eqb (p q : P) : Bool := zz (sub p q)
def leb (p q : P) : Bool := nn (sub q p)
def ltb (p q : P) : Bool := positive (sub q p)

theorem raw_nonnegative (p : P) (t : Point) (ht : ∀ i, 0 ≤ t i) (h : rawNN p=true) :
    0 ≤ eval p t := by
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
    rcases a with ⟨a,e⟩
    have hp : 0 ≤ a ∧ rawNN p=true := by simpa [rawNN] using h
    have hm := Int.mul_nonneg hp.1 (weight_nonnegative e t ht)
    have hr := ih hp.2
    simp only [eval]; omega

theorem raw_zero (p : P) (t : Point) (h : rawZZ p=true) : eval p t=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨a,e⟩
    have hp : a=0 ∧ rawZZ p=true := by simpa [rawZZ] using h
    simp [eval,hp.1,ih hp.2]

theorem raw_pos (p : P) (t : Point) (ht : ∀ i, 0 ≤ t i) (h : rawPositive p=true) :
    0 < eval p t := by
  induction p with
  | nil => simp [rawPositive] at h
  | cons a p ih =>
    rcases a with ⟨a,e⟩
    have hp : (0 ≤ a ∧ rawNN p=true) ∧
        ((e=(0,0,0) ∧ 0<a) ∨ p.any (fun b => decide (b.2=(0,0,0) ∧ 0<b.1))=true) := by
      simpa [rawPositive,rawNN] using h
    rcases hp.2 with he | he
    · have hr := raw_nonnegative p t ht hp.1.2
      rcases he with ⟨rfl,ha⟩
      simp only [eval,weight,Int.pow_zero,Int.mul_one]
      omega
    · have hr := ih (by simpa only [rawPositive,Bool.and_eq_true] using And.intro hp.1.2 he)
      have hm := Int.mul_nonneg hp.1.1 (weight_nonnegative e t ht)
      simp only [eval]; omega

theorem nonnegative (p : P) (t : Point) (ht : ∀ i, 0 ≤ t i) (h : nn p=true) :
    0 ≤ eval p t := by
  have hh := raw_nonnegative (normalize p) t ht h
  rwa [eval_normalize] at hh

theorem zero (p : P) (t : Point) (h : zz p=true) : eval p t=0 := by
  have hh := raw_zero (normalize p) t h
  rwa [eval_normalize] at hh

theorem pos (p : P) (t : Point) (ht : ∀ i, 0 ≤ t i) (h : positive p=true) :
    0 < eval p t := by
  have hh := raw_pos (normalize p) t ht h
  rwa [eval_normalize] at hh

theorem equal (p q : P) (t : Point) (h : eqb p q=true) : eval p t=eval q t := by
  have hh := zero (sub p q) t h
  rw [eval_sub] at hh; omega

theorem le (p q : P) (t : Point) (ht : ∀ i, 0 ≤ t i) (h : leb p q=true) : eval p t≤eval q t := by
  have hh := nonnegative (sub q p) t ht h
  rw [eval_sub] at hh; omega

theorem lt (p q : P) (t : Point) (ht : ∀ i, 0 ≤ t i) (h : ltb p q=true) : eval p t<eval q t := by
  have hh := pos (sub q p) t ht h
  rw [eval_sub] at hh; omega

def positivePart (p : P) : P := if nn p then p else []
def signed (p : P) : Bool := nn p || nn (neg p)

theorem eval_positivePart (p : P) (t : Point) (ht : ∀ i, 0 ≤ t i) (hs : signed p=true) :
    eval (positivePart p) t=max (eval p t) 0 := by
  by_cases hn : nn p=true
  · have hp := nonnegative p t ht hn
    simp [positivePart,hn]; omega
  · have hneg : nn (neg p)=true := by simpa [signed,hn] using hs
    have hp := nonnegative (neg p) t ht hneg
    rw [eval_neg] at hp
    simp [positivePart,hn,eval]; omega

theorem neg_neg (p : P) : neg (neg p)=p := by
  simp only [neg,List.map_map]
  have hf : (fun a : Term => (-a.1,a.2)) ∘ (fun a : Term => (-a.1,a.2)) = id := by
    funext a; rcases a with ⟨a,e⟩; simp
  rw [hf,List.map_id]

theorem signed_neg (p : P) (h : signed p=true) : signed (neg p)=true := by
  simp only [signed,neg_neg]
  simpa only [signed,Bool.or_comm] using h

def pcorr (p q : P) : P := sub (mul (positivePart p) (positivePart q))
  (mul (positivePart (neg p)) (positivePart (neg q)))

theorem eval_pcorr (p q : P) (t : Point) (ht : ∀ i, 0 ≤ t i)
    (hp : signed p=true) (hq : signed q=true) :
    eval (pcorr p q) t=correction (eval p t) (eval q t) := by
  simp only [pcorr,eval_sub,eval_mul,eval_positivePart p t ht hp,
    eval_positivePart q t ht hq,eval_positivePart (neg p) t ht (signed_neg p hp),
    eval_positivePart (neg q) t ht (signed_neg q hq),eval_neg,correction]

abbrev PMatrix := Fin 4 → Fin 4 → P
def matrix (B : PMatrix) (t : Point) : Matrix 4 := fun i j => eval (B i j) t
def six (a b c d e f : P) : PMatrix := fun i j =>
  match i.val,j.val with
  | 0,1 => a | 0,2 => b | 0,3 => c | 1,2 => d | 1,3 => e | 2,3 => f
  | 1,0 => neg a | 2,0 => neg b | 3,0 => neg c | 2,1 => neg d
  | 3,1 => neg e | 3,2 => neg f | _,_ => []

theorem matrix_six (a b c d e f : P) (t : Point) : matrix (six a b c d e f) t=
    ofSix (eval a t) (eval b t) (eval c t) (eval d t) (eval e t) (eval f t) := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [matrix,six,ofSix,eval_neg,eval]

def pmutate (B : PMatrix) (k : Fin 4) : PMatrix := fun i j =>
  if i=k ∨ j=k then neg (B i j) else add (B i j) (pcorr (B i k) (B k j))

theorem matrix_mutate (B : PMatrix) (k : Fin 4) (t : Point) (ht : ∀ i, 0≤t i)
    (hs : ∀ i j, signed (B i j)=true) :
    matrix (pmutate B k) t=mutate (matrix B t) k := by
  funext i j
  by_cases h : i=k ∨ j=k
  · simp [matrix,pmutate,mutate,h,eval_neg]
  · simp only [matrix,pmutate,mutate,h,↓reduceIte,eval_add,
      eval_pcorr _ _ t ht (hs i k) (hs k j)]

def prelabel (B : PMatrix) (p : Relabeling 4) : PMatrix := fun i j => B (p.toFun i) (p.toFun j)
def preverse (B : PMatrix) : PMatrix := fun i j => neg (B i j)

theorem matrix_relabel (B : PMatrix) (p : Relabeling 4) (t : Point) :
    matrix (prelabel B p) t=relabel (matrix B t) p := rfl

theorem matrix_reverse (B : PMatrix) (t : Point) :
    matrix (preverse B) t=reverse (matrix B t) := by
  funext i j; exact eval_neg _ _

theorem matrix_equal (B C : PMatrix) (t : Point) (h : ∀ i j, eqb (B i j) (C i j)=true) :
    matrix B t=matrix C t := by funext i j; exact equal _ _ _ (h i j)

theorem mutation_equal (B C : PMatrix) (k : Fin 4) (t : Point) (ht : ∀ i, 0≤t i)
    (hs : ∀ i j, signed (B i j)=true)
    (he : ∀ i j, eqb (pmutate B k i j) (C i j)=true) :
    mutate (matrix B t) k=matrix C t := by
  rw [←matrix_mutate B k t ht hs]
  exact matrix_equal _ _ _ he

end QuiverProofs.MultiPolynomialCertificate
