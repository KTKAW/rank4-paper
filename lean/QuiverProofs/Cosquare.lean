import QuiverProofs.Mutation
import QuiverProofs.Algebra
import QuiverProofs.Symmetry
import QuiverProofs.ForkCertificates

namespace QuiverProofs.Cosquare

/-- Fixed-size integral matrix algebra, with all four summands explicit. -/
def mul (A B : Matrix 4) : Matrix 4 := fun i j =>
  A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j

def add (A B : Matrix 4) : Matrix 4 := fun i j => A i j + B i j
def scale (a : Int) (A : Matrix 4) : Matrix 4 := fun i j => a * A i j
def zero : Matrix 4 := fun _ _ => 0
def one : Matrix 4 := fun i j => if i = j then 1 else 0
def transpose (A : Matrix 4) : Matrix 4 := fun i j => A j i

def mat4 (a b c d e f g h i j k l m n o p : Int) : Matrix 4 := fun r s =>
  match r.val,s.val with
  | 0,0 => a | 0,1 => b | 0,2 => c | 0,3 => d
  | 1,0 => e | 1,1 => f | 1,2 => g | 1,3 => h
  | 2,0 => i | 2,1 => j | 2,2 => k | 2,3 => l
  | 3,0 => m | 3,1 => n | 3,2 => o | _,_ => p

def determinant (A : Matrix 4) : Int := Algebra.det4
  (A 0 0) (A 0 1) (A 0 2) (A 0 3)
  (A 1 0) (A 1 1) (A 1 2) (A 1 3)
  (A 2 0) (A 2 1) (A 2 2) (A 2 3)
  (A 3 0) (A 3 1) (A 3 2) (A 3 3)

theorem mul_assoc (A B C : Matrix 4) : mul (mul A B) C = mul A (mul B C) := by
  funext i j
  simp only [mul]
  grind

theorem mul_one (A : Matrix 4) : mul A one = A := by
  funext i j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hj with rfl|rfl|rfl|rfl <;> simp [mul,one]

theorem one_mul (A : Matrix 4) : mul one A = A := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> simp [mul,one]

theorem mul_zero (A : Matrix 4) : mul A zero = zero := by funext i j; simp [mul,zero]
theorem zero_mul (A : Matrix 4) : mul zero A = zero := by funext i j; simp [mul,zero]

theorem mul_add (A B C : Matrix 4) : mul A (add B C) = add (mul A B) (mul A C) := by
  funext i j; simp only [mul,add]; grind

theorem add_mul (A B C : Matrix 4) : mul (add A B) C = add (mul A C) (mul B C) := by
  funext i j; simp only [mul,add]; grind

theorem mul_scale (A B : Matrix 4) (a : Int) : mul A (scale a B) = scale a (mul A B) := by
  funext i j; simp only [mul,scale]; grind

theorem scale_mul (A B : Matrix 4) (a : Int) : mul (scale a A) B = scale a (mul A B) := by
  funext i j; simp only [mul,scale]; grind

/-- Integer polynomial coefficients, in increasing degree, evaluated by Horner recursion.
Every finite integer coefficient list is allowed, without a degree bound. -/
def evalPoly (A : Matrix 4) : List Int → Matrix 4
  | [] => zero
  | a::cs => add (scale a one) (mul A (evalPoly A cs))

theorem polynomial_intertwining (A B P : Matrix 4) (h : mul A P = mul P B)
    (coefficients : List Int) :
    mul (evalPoly A coefficients) P = mul P (evalPoly B coefficients) := by
  induction coefficients with
  | nil => simp [evalPoly,zero_mul,mul_zero]
  | cons a cs ih =>
    simp only [evalPoly,add_mul,mul_add,scale_mul,mul_scale,one_mul,mul_one]
    rw [mul_assoc,ih,← mul_assoc,h,mul_assoc]

/-- An explicit two-sided integer inverse avoids appealing to determinant theory. -/
def IntegralSimilarity (A B : Matrix 4) : Prop :=
  ∃ P Pinv : Matrix 4, mul P Pinv = one ∧ mul Pinv P = one ∧ mul A P = mul P B

theorem polynomial_integral_similarity (A B : Matrix 4) (h : IntegralSimilarity A B)
    (coefficients : List Int) :
    IntegralSimilarity (evalPoly A coefficients) (evalPoly B coefficients) := by
  rcases h with ⟨P,Pinv,hp,hi,he⟩
  exact ⟨P,Pinv,hp,hi,polynomial_intertwining A B P he coefficients⟩

theorem conjugacy_of_intertwining (A B P Pinv : Matrix 4)
    (hinv : mul Pinv P = one) (he : mul A P = mul P B) :
    mul (mul Pinv A) P = B := by
  rw [mul_assoc,he,← mul_assoc,hinv,one_mul]

/-- The manuscript convention U_ij = -b_ij above the diagonal. -/
def companion (a b c d e f : Int) : Matrix 4 :=
  mat4 1 (-a) (-b) (-c) 0 1 (-d) (-e) 0 0 1 (-f) 0 0 0 1

def companionInverse (a b c d e f : Int) : Matrix 4 :=
  mat4 1 a (b+a*d) (c+a*e+b*f+a*d*f) 0 1 d (e+d*f) 0 0 1 f 0 0 0 1

theorem companion_inverse_right (a b c d e f : Int) :
    mul (companion a b c d e f) (companionInverse a b c d e f) = one := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [mul,companion,companionInverse,mat4,one] <;> grind

theorem companion_inverse_left (a b c d e f : Int) :
    mul (companionInverse a b c d e f) (companion a b c d e f) = one := by
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
    simp [mul,companion,companionInverse,mat4,one] <;> grind

/-- C = U^(-T) U, computed with a proved exact integer inverse. -/
def cosquare (a b c d e f : Int) : Matrix 4 :=
  mul (transpose (companionInverse a b c d e f)) (companion a b c d e f)

/-- Ordered companion data are extracted from the actual exchange matrix. -/
def orderedCosquare (B : Matrix 4) (order : Relabeling 4) : Matrix 4 :=
  let R := relabel B order
  cosquare (R 0 1) (R 0 2) (R 0 3) (R 1 2) (R 1 3) (R 2 3)

def identityOrder : Relabeling 4 where
  toFun i := i
  invFun i := i
  left_inv _ := rfl
  right_inv _ := rfl

def strongOrder : Relabeling 4 where
  toFun i := match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1
  invFun i := match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1
  left_inv := by decide
  right_inv := by decide

def strongQ : Matrix 4 := ofSix (-3) (-3) 3 (-14) (-6) (-3)
def strongA : Matrix 4 := ofSix 0 1 4 13 1 0

def strongP : Matrix 4 :=
  mat4 (-566) (-1534) 109 122 (-248) (-739) 53 52 (-42) (-210) 16 7 (-7) (-16) 5 2


def strongPinv : Matrix 4 :=
  mat4 22747 (-58694) 40684 (-3917) (-2497) 6443 (-4466) 430
    (-9023) 23282 (-16138) 1554 82196 (-212090) 147011 (-14154)

theorem strongP_determinant : determinant strongP = -1 := by decide

theorem strongP_inverse_right : mul strongP strongPinv = one := by
  funext i j; revert i j; decide

theorem strongP_inverse_left : mul strongPinv strongP = one := by
  funext i j; revert i j; decide

theorem strong_cosquare_intertwining :
    mul (orderedCosquare strongQ strongOrder) strongP =
      mul strongP (orderedCosquare strongA identityOrder) := by
  funext i j; revert i j; decide

theorem strong_cosquare_similarity :
    IntegralSimilarity (orderedCosquare strongQ strongOrder) (orderedCosquare strongA identityOrder) :=
  ⟨strongP,strongPinv,strongP_inverse_right,strongP_inverse_left,strong_cosquare_intertwining⟩

theorem strong_A_acyclic : Acyclic strongA := by
  exact ⟨fun i => i.val, by decide⟩

theorem strong_Q_NMA : ¬ MutationAcyclic strongQ := ForkCertificates.Core17.nma

/-- A complete semantic counterexample: a genuinely NMA exchange matrix whose
ordered cosquare is integrally similar to an acyclic exchange matrix's cosquare. -/
theorem NMA_cosquare_matches_acyclic :
    ¬ MutationAcyclic strongQ ∧ Acyclic strongA ∧
    IntegralSimilarity (orderedCosquare strongQ strongOrder) (orderedCosquare strongA identityOrder) :=
  ⟨strong_Q_NMA,strong_A_acyclic,strong_cosquare_similarity⟩

/-- The same explicit unimodular P works for every integer polynomial degree. -/
theorem strong_all_polynomials_intertwine (coefficients : List Int) :
    mul (evalPoly (orderedCosquare strongQ strongOrder) coefficients) strongP =
      mul strongP (evalPoly (orderedCosquare strongA identityOrder) coefficients) :=
  polynomial_intertwining _ _ _ strong_cosquare_intertwining coefficients

theorem strong_all_polynomials_similar (coefficients : List Int) :
    IntegralSimilarity
      (evalPoly (orderedCosquare strongQ strongOrder) coefficients)
      (evalPoly (orderedCosquare strongA identityOrder) coefficients) :=
  polynomial_integral_similarity _ _ strong_cosquare_similarity coefficients

theorem strong_all_polynomials_conjugate (coefficients : List Int) :
    mul (mul strongPinv (evalPoly (orderedCosquare strongQ strongOrder) coefficients)) strongP =
      evalPoly (orderedCosquare strongA identityOrder) coefficients :=
  conjugacy_of_intertwining _ _ _ _ strongP_inverse_left
    (strong_all_polynomials_intertwine coefficients)

theorem strong_markov_matches :
    Algebra.markov 3 (-3) (-3) 3 6 14 = 187 ∧
    Algebra.markov 0 1 4 13 1 0 = 187 := by decide

theorem strong_exchange_determinants_match :
    determinant strongQ = 2601 ∧ determinant strongA = 2601 := by decide

theorem strong_symmetric_companion_determinants_match :
    determinant (add (companion 3 (-3) (-3) 3 6 14) (transpose (companion 3 (-3) (-3) 3 6 14))) = 1869 ∧
    determinant (add (companion 0 1 4 13 1 0) (transpose (companion 0 1 4 13 1 0))) = 1869 := by decide

/-- The separate delayed-failure seed's exact cosquare witness. This module does
not infer its proper-transport depth from the numerical similarity. -/
def delayedOrder : Relabeling 4 where
  toFun i := match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2
  invFun i := match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2
  left_inv := by decide
  right_inv := by decide

def delayedQ : Matrix 4 := ofSix 0 (-1) 3 (-2) (-2) (-2)
def delayedA : Matrix 4 := ofSix 0 0 4 2 1 1

def delayedP : Matrix 4 := mat4 0 2 (-6) 1 (-1) 3 (-5) 0 (-1) 1 (-2) 3 1 (-6) 9 5

def delayedPinv : Matrix 4 := mat4 4 (-61) 37 (-23) 3 (-55) 34 (-21) 1 (-21) 13 (-8) 1 (-16) 10 (-6)

theorem delayedP_determinant : determinant delayedP = 1 := by decide

theorem delayedP_inverse_right : mul delayedP delayedPinv = one := by
  funext i j; revert i j; decide

theorem delayedP_inverse_left : mul delayedPinv delayedP = one := by
  funext i j; revert i j; decide

theorem delayed_Q_cosquare_printed : orderedCosquare delayedQ delayedOrder =
    mat4 1 0 (-3) 1 0 1 2 2 3 (-2) (-12) (-3) 5 (-6) (-25) (-10) := by
  funext i j; revert i j; decide

theorem delayed_A_cosquare_printed : orderedCosquare delayedA identityOrder =
    mat4 1 0 0 (-4) 0 1 (-2) (-1) 0 2 (-3) (-3) 4 3 (-5) (-19) := by
  funext i j; revert i j; decide

theorem delayed_cosquare_intertwining :
    mul (orderedCosquare delayedQ delayedOrder) delayedP =
      mul delayedP (orderedCosquare delayedA identityOrder) := by
  funext i j; revert i j; decide

theorem delayed_cosquare_similarity :
    IntegralSimilarity (orderedCosquare delayedQ delayedOrder) (orderedCosquare delayedA identityOrder) :=
  ⟨delayedP,delayedPinv,delayedP_inverse_right,delayedP_inverse_left,delayed_cosquare_intertwining⟩

theorem delayed_all_polynomials_similar (coefficients : List Int) :
    IntegralSimilarity
      (evalPoly (orderedCosquare delayedQ delayedOrder) coefficients)
      (evalPoly (orderedCosquare delayedA identityOrder) coefficients) :=
  polynomial_integral_similarity _ _ delayed_cosquare_similarity coefficients

theorem delayed_A_acyclic : Acyclic delayedA := by
  exact ⟨fun i => i.val, by decide⟩

end QuiverProofs.Cosquare
