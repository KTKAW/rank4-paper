import Rank4Formula.FormulaSubstitution
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
Exact polynomial mutation on all sign chambers of the six upper entries.
The coordinate order is 01, 02, 03, 12, 13, 23.  Every coordinate is an
unrestricted integer; the three signs include zero as a separate case.
-/

namespace Rank4Round3
open Rank4Formula QuiverProofs

abbrev Sign3 := Fin 3
abbrev SignPattern := Fin 6 → Sign3

private theorem sign3_cases (s : Sign3) : s = 0 ∨ s = 1 ∨ s = 2 := by
  have h : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

def SignMatch (s : Sign3) (x : Int) : Prop :=
  match s.val with
  | 0 => x < 0
  | 1 => x = 0
  | _ => 0 < x

def Chamber (s : SignPattern) (q : SixTuple) : Prop :=
  ∀ i : Fin 6, SignMatch (s i) (q i)

def signOf (x : Int) : Sign3 :=
  if x < 0 then 0 else if x = 0 then 1 else 2

theorem signOf_match (x : Int) : SignMatch (signOf x) x := by
  by_cases hneg : x < 0
  · simp [signOf, SignMatch, hneg]
  · by_cases hzero : x = 0
    · simp [signOf, hzero, SignMatch]
    · simp [signOf, hneg, hzero, SignMatch]
      omega

theorem chambers_cover (q : SixTuple) :
    ∃ s : SignPattern, Chamber s q := by
  exact ⟨fun i => signOf (q i), fun i => signOf_match (q i)⟩

theorem signMatch_unique (s t : Sign3) (x : Int)
    (hs : SignMatch s x) (ht : SignMatch t x) : s = t := by
  have es := sign3_cases s
  have et := sign3_cases t
  rcases es with rfl | rfl | rfl <;>
    rcases et with rfl | rfl | rfl <;>
      simp [SignMatch] at hs ht ⊢ <;> omega

theorem chamber_unique (s t : SignPattern) (q : SixTuple)
    (hs : Chamber s q) (ht : Chamber t q) : s = t := by
  funext i
  exact signMatch_unique (s i) (t i) (q i) (hs i) (ht i)

theorem sign_pattern_count : Fintype.card SignPattern = 729 := by
  simp [SignPattern]

def flipSign (s : Sign3) : Sign3 :=
  match s.val with
  | 0 => 2
  | 1 => 1
  | _ => 0

theorem signMatch_flip (s : Sign3) (x : Int) :
    SignMatch (flipSign s) (-x) ↔ SignMatch s x := by
  have hs := sign3_cases s
  rcases hs with rfl | rfl | rfl <;>
    simp [flipSign, SignMatch]

inductive MutationPoly where
  | zero : MutationPoly
  | coord : Fin 6 → MutationPoly
  | neg : MutationPoly → MutationPoly
  | add : MutationPoly → MutationPoly → MutationPoly
  | mul : MutationPoly → MutationPoly → MutationPoly
  deriving Repr

def MutationPoly.evalInt : MutationPoly → SixTuple → Int
  | .zero, _ => 0
  | .coord i, q => q i
  | .neg p, q => -(p.evalInt q)
  | .add p r, q => p.evalInt q + r.evalInt q
  | .mul p r, q => p.evalInt q * r.evalInt q

def MutationPoly.toPolyTerm : MutationPoly → PolyTerm
  | .zero => .const 0
  | .coord i => .coord i
  | .neg p => .neg p.toPolyTerm
  | .add p r => .add p.toPolyTerm r.toPolyTerm
  | .mul p r => .mul p.toPolyTerm r.toPolyTerm

theorem MutationPoly.toPolyTerm_eval (p : MutationPoly) (q : SixTuple) :
    p.toPolyTerm.eval q = (p.evalInt q : Rat) := by
  induction p with
  | zero => rfl
  | coord i => rfl
  | neg p ih => simp [toPolyTerm, PolyTerm.eval, evalInt, ih]
  | add p r ihp ihr => simp [toPolyTerm, PolyTerm.eval, evalInt, ihp, ihr]
  | mul p r ihp ihr => simp [toPolyTerm, PolyTerm.eval, evalInt, ihp, ihr]

def signedTerm (i : Fin 6) (reversed : Bool) : MutationPoly :=
  if reversed then .neg (.coord i) else .coord i

def signedValue (q : SixTuple) (i : Fin 6) (reversed : Bool) : Int :=
  if reversed then -q i else q i

def signedSign (s : SignPattern) (i : Fin 6) (reversed : Bool) : Sign3 :=
  if reversed then flipSign (s i) else s i

theorem signedTerm_eval (q : SixTuple) (i : Fin 6) (reversed : Bool) :
    (signedTerm i reversed).evalInt q = signedValue q i reversed := by
  cases reversed <;> rfl

theorem signedSign_match (s : SignPattern) (q : SixTuple)
    (h : Chamber s q) (i : Fin 6) (reversed : Bool) :
    SignMatch (signedSign s i reversed) (signedValue q i reversed) := by
  cases reversed with
  | false => exact h i
  | true => exact (signMatch_flip (s i) (q i)).mpr (h i)

def correctionValue (sx sy : Sign3) (x y : Int) : Int :=
  if sx = 2 ∧ sy = 2 then x * y
  else if sx = 0 ∧ sy = 0 then -(x * y)
  else 0

def correctionTerm (sx sy : Sign3)
    (x y : MutationPoly) : MutationPoly :=
  if sx = 2 ∧ sy = 2 then .mul x y
  else if sx = 0 ∧ sy = 0 then .neg (.mul x y)
  else .zero

theorem correctionTerm_eval (sx sy : Sign3) (x y : MutationPoly)
    (q : SixTuple) :
    (correctionTerm sx sy x y).evalInt q =
      correctionValue sx sy (x.evalInt q) (y.evalInt q) := by
  by_cases hpos : sx = 2 ∧ sy = 2
  · simp [correctionTerm, correctionValue, hpos, MutationPoly.evalInt]
  · by_cases hneg : sx = 0 ∧ sy = 0
    · simp [correctionTerm, correctionValue, hneg, MutationPoly.evalInt]
    · simp [correctionTerm, correctionValue, hpos, hneg, MutationPoly.evalInt]

theorem correctionValue_eq (sx sy : Sign3) (x y : Int)
    (hx : SignMatch sx x) (hy : SignMatch sy y) :
    correctionValue sx sy x y = correction x y := by
  have hsx := sign3_cases sx
  have hsy := sign3_cases sy
  rcases hsx with rfl | rfl | rfl <;>
    rcases hsy with rfl | rfl | rfl <;>
      simp [SignMatch] at hx hy
  all_goals
    have hxp : max x 0 = (if 0 < x then x else 0) := by
      by_cases h : 0 < x <;> simp [h] <;> omega
    have hxn : max (-x) 0 = (if x < 0 then -x else 0) := by
      by_cases h : x < 0 <;> simp [h] <;> omega
    have hyp : max y 0 = (if 0 < y then y else 0) := by
      by_cases h : 0 < y <;> simp [h] <;> omega
    have hyn : max (-y) 0 = (if y < 0 then -y else 0) := by
      by_cases h : y < 0 <;> simp [h] <;> omega
    simp [correctionValue, correction, hxp, hxn, hyp, hyn, hx, hy]
      <;> split_ifs <;> omega

def chamberCorrectionTerm (s : SignPattern)
    (i : Fin 6) (ri : Bool) (j : Fin 6) (rj : Bool) : MutationPoly :=
  correctionTerm (signedSign s i ri) (signedSign s j rj)
    (signedTerm i ri) (signedTerm j rj)

theorem chamberCorrectionTerm_eval (s : SignPattern) (q : SixTuple)
    (h : Chamber s q) (i : Fin 6) (ri : Bool) (j : Fin 6) (rj : Bool) :
    (chamberCorrectionTerm s i ri j rj).evalInt q =
      correction (signedValue q i ri) (signedValue q j rj) := by
  simp only [chamberCorrectionTerm, correctionTerm_eval,
    signedTerm_eval]
  exact correctionValue_eq _ _ _ _
    (signedSign_match s q h i ri) (signedSign_match s q h j rj)

/-! The 24 upper-entry expressions, grouped by mutated vertex. -/
def mutationTerm (k : Fin 4) (s : SignPattern) (i : Fin 6) : MutationPoly :=
  match k.val, i.val with
  | 0, 0 => .neg (.coord 0)
  | 0, 1 => .neg (.coord 1)
  | 0, 2 => .neg (.coord 2)
  | 0, 3 => .add (.coord 3) (chamberCorrectionTerm s 0 true 1 false)
  | 0, 4 => .add (.coord 4) (chamberCorrectionTerm s 0 true 2 false)
  | 0, _ => .add (.coord 5) (chamberCorrectionTerm s 1 true 2 false)
  | 1, 0 => .neg (.coord 0)
  | 1, 1 => .add (.coord 1) (chamberCorrectionTerm s 0 false 3 false)
  | 1, 2 => .add (.coord 2) (chamberCorrectionTerm s 0 false 4 false)
  | 1, 3 => .neg (.coord 3)
  | 1, 4 => .neg (.coord 4)
  | 1, _ => .add (.coord 5) (chamberCorrectionTerm s 3 true 4 false)
  | 2, 0 => .add (.coord 0) (chamberCorrectionTerm s 1 false 3 true)
  | 2, 1 => .neg (.coord 1)
  | 2, 2 => .add (.coord 2) (chamberCorrectionTerm s 1 false 5 false)
  | 2, 3 => .neg (.coord 3)
  | 2, 4 => .add (.coord 4) (chamberCorrectionTerm s 3 false 5 false)
  | 2, _ => .neg (.coord 5)
  | _, 0 => .add (.coord 0) (chamberCorrectionTerm s 2 false 4 true)
  | _, 1 => .add (.coord 1) (chamberCorrectionTerm s 2 false 5 true)
  | _, 2 => .neg (.coord 2)
  | _, 3 => .add (.coord 3) (chamberCorrectionTerm s 4 false 5 true)
  | _, 4 => .neg (.coord 4)
  | _, _ => .neg (.coord 5)

def mutationTuple (k : Fin 4) (s : SignPattern) (q : SixTuple) : SixTuple :=
  fun i => (mutationTerm k s i).evalInt q

def mutationTerms (k : Fin 4) (s : SignPattern) : Fin 6 → PolyTerm :=
  fun i => (mutationTerm k s i).toPolyTerm

theorem mutationTerms_eval (k : Fin 4) (s : SignPattern)
    (q : SixTuple) (i : Fin 6) :
    (mutationTerms k s i).eval q = (mutationTuple k s q i : Rat) := by
  exact MutationPoly.toPolyTerm_eval (mutationTerm k s i) q

def upperEntry (B : Matrix 4) (i : Fin 6) : Int :=
  match i.val with
  | 0 => B 0 1
  | 1 => B 0 2
  | 2 => B 0 3
  | 3 => B 1 2
  | 4 => B 1 3
  | _ => B 2 3

def upperTuple (B : Matrix 4) : SixTuple :=
  fun i => upperEntry B i

theorem upperTuple_ofTuple (q : SixTuple) :
    upperTuple (ofTuple q) = q := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [upperTuple, upperEntry, ofTuple, ofSix]

theorem ofTuple_upperTuple (B : Matrix 4) (hB : SkewSymmetric B) :
    ofTuple (upperTuple B) = B := by
  simpa [ofTuple, upperTuple, upperEntry] using
    ofSix_reconstruct B hB

theorem mutationTuple_upperEntry (k : Fin 4) (s : SignPattern)
    (q : SixTuple) (h : Chamber s q) (i : Fin 6) :
    mutationTuple k s q i = upperEntry (mutate (ofTuple q) k) i := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases hk with rfl | rfl | rfl | rfl <;>
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mutationTuple, mutationTerm, MutationPoly.evalInt,
        chamberCorrectionTerm_eval s q h, upperEntry, mutate,
        ofTuple, ofSix, signedValue]

theorem mutationTuple_matrix (k : Fin 4) (s : SignPattern)
    (q : SixTuple) (h : Chamber s q) :
    ofTuple (mutationTuple k s q) = mutate (ofTuple q) k := by
  have hq : SkewSymmetric (ofTuple q) :=
    ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  have hr := ofSix_reconstruct (mutate (ofTuple q) k)
    (mutation_preserves_skew (ofTuple q) k hq)
  simpa [ofTuple, upperEntry,
    mutationTuple_upperEntry k s q h] using hr

theorem skew_matrix_polynomial_mutation (B : Matrix 4)
    (hB : SkewSymmetric B) (k : Fin 4) :
    ofTuple (mutationTuple k
      (fun i => signOf (upperTuple B i)) (upperTuple B)) = mutate B k := by
  have hch : Chamber (fun i => signOf (upperTuple B i)) (upperTuple B) :=
    fun i => signOf_match (upperTuple B i)
  simpa [ofTuple_upperTuple B hB] using
    mutationTuple_matrix k (fun i => signOf (upperTuple B i))
      (upperTuple B) hch

def mutatedUpper (q : SixTuple) (k : Fin 4) : SixTuple :=
  fun i => upperEntry (mutate (ofTuple q) k) i

theorem mutatedUpper_matrix (q : SixTuple) (k : Fin 4) :
    ofTuple (mutatedUpper q k) = mutate (ofTuple q) k := by
  have hq : SkewSymmetric (ofTuple q) :=
    ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  simpa [ofTuple, mutatedUpper, upperEntry] using
    ofSix_reconstruct (mutate (ofTuple q) k)
      (mutation_preserves_skew (ofTuple q) k hq)

theorem mutationTuple_eq_mutatedUpper (k : Fin 4) (s : SignPattern)
    (q : SixTuple) (h : Chamber s q) :
    mutationTuple k s q = mutatedUpper q k := by
  funext i
  exact mutationTuple_upperEntry k s q h i

theorem all_vertices_all_chambers (q : SixTuple) :
    ∃ s : SignPattern, Chamber s q ∧
      ∀ k : Fin 4, ofTuple (mutationTuple k s q) = mutate (ofTuple q) k := by
  obtain ⟨s, hs⟩ := chambers_cover q
  exact ⟨s, hs, fun k => mutationTuple_matrix k s q hs⟩

theorem vertex_chamber_pair_count :
    Fintype.card (Fin 4 × SignPattern) = 2916 := by
  simp

theorem formula_subst_eval (F : Formula) (k : Fin 4)
    (s : SignPattern) (q : SixTuple) :
    (F.subst (mutationTerms k s)).eval q =
      F.eval (mutationTuple k s q) := by
  exact Formula.subst_eval_of_target (mutationTerms k s) F q
    (mutationTuple k s q) (mutationTerms_eval k s q)

/-- Every polynomial-sign formula pulls back exactly along mutation on the
chosen chamber. The target formula may itself impose any six output signs. -/
theorem formula_mutation_pullback (F : Formula) (k : Fin 4)
    (s : SignPattern) (q : SixTuple) (h : Chamber s q) :
    (F.subst (mutationTerms k s)).eval q =
      F.eval (mutatedUpper q k) := by
  rw [formula_subst_eval, mutationTuple_eq_mutatedUpper k s q h]

def strictAtom (p r : PolyTerm) : Formula :=
  .not (.lessEq r p)

theorem strictAtom_eval (p r : PolyTerm) (q : SixTuple) :
    (strictAtom p r).eval q = true ↔ p.eval q < r.eval q := by
  simp [strictAtom, Formula.eval, not_le]

theorem mutation_equal_pullback (p r : PolyTerm) (k : Fin 4)
    (s : SignPattern) (q : SixTuple) (h : Chamber s q) :
    ((Formula.equal p r).subst (mutationTerms k s)).eval q = true ↔
      p.eval (mutatedUpper q k) = r.eval (mutatedUpper q k) := by
  rw [formula_mutation_pullback _ k s q h]
  simp [Formula.eval]

theorem mutation_le_pullback (p r : PolyTerm) (k : Fin 4)
    (s : SignPattern) (q : SixTuple) (h : Chamber s q) :
    ((Formula.lessEq p r).subst (mutationTerms k s)).eval q = true ↔
      p.eval (mutatedUpper q k) ≤ r.eval (mutatedUpper q k) := by
  rw [formula_mutation_pullback _ k s q h]
  simp [Formula.eval]

theorem mutation_lt_pullback (p r : PolyTerm) (k : Fin 4)
    (s : SignPattern) (q : SixTuple) (h : Chamber s q) :
    ((strictAtom p r).subst (mutationTerms k s)).eval q = true ↔
      p.eval (mutatedUpper q k) < r.eval (mutatedUpper q k) := by
  rw [formula_mutation_pullback _ k s q h]
  exact strictAtom_eval p r (mutatedUpper q k)

def signAtom (s : Sign3) (i : Fin 6) : Formula :=
  match s.val with
  | 0 => strictAtom (.coord i) (.const 0)
  | 1 => .equal (.coord i) (.const 0)
  | _ => strictAtom (.const 0) (.coord i)

theorem signAtom_eval (s : Sign3) (i : Fin 6) (q : SixTuple) :
    (signAtom s i).eval q = true ↔ SignMatch s (q i) := by
  have hs := sign3_cases s
  rcases hs with rfl | rfl | rfl <;>
    simp [signAtom, SignMatch, strictAtom_eval, Formula.eval, PolyTerm.eval]
      <;> norm_cast

def chamberSyntax (s : SignPattern) : Formula :=
  .and (signAtom (s 0) 0)
    (.and (signAtom (s 1) 1)
      (.and (signAtom (s 2) 2)
        (.and (signAtom (s 3) 3)
          (.and (signAtom (s 4) 4) (signAtom (s 5) 5)))))

theorem chamberSyntax_eval (s : SignPattern) (q : SixTuple) :
    (chamberSyntax s).eval q = true ↔ Chamber s q := by
  simp only [chamberSyntax, Formula.eval, Bool.and_eq_true, signAtom_eval]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

/-- A finite Formula AST for the one-step preimage of any target formula,
with the exact input chamber built into the syntax. -/
def pullbackSyntax (k : Fin 4) (s : SignPattern) (F : Formula) : Formula :=
  .and (chamberSyntax s) (F.subst (mutationTerms k s))

theorem pullbackSyntax_correct (k : Fin 4) (s : SignPattern)
    (F : Formula) (q : SixTuple) :
    (pullbackSyntax k s F).eval q = true ↔
      Chamber s q ∧ F.eval (mutatedUpper q k) = true := by
  simp only [pullbackSyntax, Formula.eval, Bool.and_eq_true,
    chamberSyntax_eval]
  constructor
  · rintro ⟨hs, hF⟩
    exact ⟨hs, (formula_mutation_pullback F k s q hs) ▸ hF⟩
  · rintro ⟨hs, hF⟩
    exact ⟨hs, (formula_mutation_pullback F k s q hs).symm ▸ hF⟩

/-- In particular, a target's six coordinate signs are all substituted.
No output chamber is inferred solely from the input chamber. -/
theorem output_chamber_pullback (k : Fin 4) (s t : SignPattern)
    (q : SixTuple) :
    (pullbackSyntax k s (chamberSyntax t)).eval q = true ↔
      Chamber s q ∧ Chamber t (mutatedUpper q k) := by
  rw [pullbackSyntax_correct]
  simp only [chamberSyntax_eval]

/-- Simultaneous target polynomial conditions and all six target sign guards. -/
theorem guarded_target_pullback (k : Fin 4) (s t : SignPattern)
    (F : Formula) (q : SixTuple) :
    (pullbackSyntax k s (.and (chamberSyntax t) F)).eval q = true ↔
      Chamber s q ∧ Chamber t (mutatedUpper q k) ∧
        F.eval (mutatedUpper q k) = true := by
  rw [pullbackSyntax_correct]
  simp only [Formula.eval, Bool.and_eq_true, chamberSyntax_eval]

/-- The 729 chamber pullbacks for one vertex cover its entire one-step
preimage, with no exceptional input on a zero boundary. -/
theorem all_chamber_pullbacks_iff (F : Formula) (k : Fin 4)
    (q : SixTuple) :
    (∃ s : SignPattern, (pullbackSyntax k s F).eval q = true) ↔
      F.eval (mutatedUpper q k) = true := by
  constructor
  · rintro ⟨s, hs⟩
    exact (pullbackSyntax_correct k s F q).mp hs |>.2
  · intro hF
    obtain ⟨s, hs⟩ := chambers_cover q
    exact ⟨s, (pullbackSyntax_correct k s F q).mpr ⟨hs, hF⟩⟩

/-- All 2,916 vertex/chamber cases are exact preimages of their targets. -/
theorem all_vertex_chamber_pullbacks_iff (F : Formula) (q : SixTuple) :
    (∃ k : Fin 4, ∃ s : SignPattern,
      (pullbackSyntax k s F).eval q = true) ↔
      ∃ k : Fin 4, F.eval (mutatedUpper q k) = true := by
  simp only [all_chamber_pullbacks_iff]

/-- A target formula known to imply MA gives a sound one-step certificate on
every vertex and every chamber. -/
theorem pullback_MA_of_target (F : Formula)
    (hF : ∀ r : SixTuple, F.eval r = true → MutationAcyclic (ofTuple r))
    (k : Fin 4) (s : SignPattern) (q : SixTuple)
    (h : (pullbackSyntax k s F).eval q = true) :
    MutationAcyclic (ofTuple q) := by
  have htarget := hF (mutatedUpper q k) ((pullbackSyntax_correct k s F q).mp h).2
  rw [mutatedUpper_matrix] at htarget
  exact (mutationAcyclic_iff (ofTuple q) k).mp htarget

#print axioms chambers_cover
#print axioms sign_pattern_count
#print axioms mutationTuple_matrix
#print axioms skew_matrix_polynomial_mutation
#print axioms vertex_chamber_pair_count
#print axioms formula_mutation_pullback
#print axioms mutation_equal_pullback
#print axioms mutation_le_pullback
#print axioms mutation_lt_pullback
#print axioms output_chamber_pullback
#print axioms guarded_target_pullback
#print axioms all_chamber_pullbacks_iff
#print axioms all_vertex_chamber_pullbacks_iff
#print axioms pullback_MA_of_target

end Rank4Round3
