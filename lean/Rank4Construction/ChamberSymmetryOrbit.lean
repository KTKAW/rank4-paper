import Rank4Construction.ChamberFormulaSyntaxCore
import QuiverProofs.Symmetry

/-!
Pulling an algebraic formula back along a vertex relabeling and optional
global arrow reversal.  The pullback is itself a finite formula AST: each of
its six coordinate leaves is replaced by one signed original coordinate.
-/

namespace Rank4Construction
open Rank4Formula QuiverProofs

/-- An entry of the skew matrix, expressed as a polynomial term in its six
upper-triangular coordinates. -/
def edgeTerm (i j : Fin 4) : PolyTerm :=
  match i.val, j.val with
  | 0, 1 => .coord 0 | 0, 2 => .coord 1 | 0, 3 => .coord 2
  | 1, 2 => .coord 3 | 1, 3 => .coord 4 | 2, 3 => .coord 5
  | 1, 0 => .neg (.coord 0) | 2, 0 => .neg (.coord 1)
  | 3, 0 => .neg (.coord 2) | 2, 1 => .neg (.coord 3)
  | 3, 1 => .neg (.coord 4) | 3, 2 => .neg (.coord 5)
  | _, _ => .const 0

theorem edgeTerm_eval (i j : Fin 4) (q : SixTuple) :
    (edgeTerm i j).eval q = (ofTuple q i j : Rat) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [edgeTerm, ofTuple, ofSix, PolyTerm.eval]

/-- The permuted matrix, optionally with all arrows reversed. -/
def orbitMatrix (p : Relabeling 4) (flip : Bool) (q : SixTuple) : Matrix 4 :=
  if flip then reverse (relabel (ofTuple q) p) else relabel (ofTuple q) p

/-- Its six upper-triangular entries. -/
def orbitTuple (p : Relabeling 4) (flip : Bool) (q : SixTuple) : SixTuple :=
  let B := orbitMatrix p flip q
  fun i => match i.val with
    | 0 => B 0 1 | 1 => B 0 2 | 2 => B 0 3
    | 3 => B 1 2 | 4 => B 1 3 | _ => B 2 3

def orbitCoordTerm (p : Relabeling 4) (flip : Bool) (k : Fin 6) : PolyTerm :=
  let signed (i j : Fin 4) :=
    if flip then .neg (edgeTerm (p.toFun i) (p.toFun j))
    else edgeTerm (p.toFun i) (p.toFun j)
  match k.val with
    | 0 => signed 0 1 | 1 => signed 0 2 | 2 => signed 0 3
    | 3 => signed 1 2 | 4 => signed 1 3 | _ => signed 2 3

theorem orbitCoordTerm_eval (p : Relabeling 4) (flip : Bool)
    (k : Fin 6) (q : SixTuple) :
    (orbitCoordTerm p flip k).eval q = (orbitTuple p flip q k : Rat) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases flip <;>
      simp [orbitCoordTerm, orbitTuple, orbitMatrix, reverse, relabel,
        PolyTerm.eval, edgeTerm_eval]

/-- Substitution into a polynomial AST, with no matrix or mutation call in
the resulting AST. -/
def orbitPolyTerm (p : Relabeling 4) (flip : Bool) : PolyTerm → PolyTerm
  | .const c => .const c
  | .coord k => orbitCoordTerm p flip k
  | .neg t => .neg (orbitPolyTerm p flip t)
  | .add s t => .add (orbitPolyTerm p flip s) (orbitPolyTerm p flip t)
  | .mul s t => .mul (orbitPolyTerm p flip s) (orbitPolyTerm p flip t)

theorem orbitPolyTerm_eval (p : Relabeling 4) (flip : Bool)
    (t : PolyTerm) (q : SixTuple) :
    (orbitPolyTerm p flip t).eval q = t.eval (orbitTuple p flip q) := by
  induction t with
  | const c => rfl
  | coord k => exact orbitCoordTerm_eval p flip k q
  | neg t ih => simp [orbitPolyTerm, PolyTerm.eval, ih]
  | add s t ihs iht => simp [orbitPolyTerm, PolyTerm.eval, ihs, iht]
  | mul s t ihs iht => simp [orbitPolyTerm, PolyTerm.eval, ihs, iht]

/-- Pullback of a finite polynomial-sign formula. -/
def orbitFormula (p : Relabeling 4) (flip : Bool) : Formula → Formula
  | .equal s t => .equal (orbitPolyTerm p flip s) (orbitPolyTerm p flip t)
  | .lessEq s t => .lessEq (orbitPolyTerm p flip s) (orbitPolyTerm p flip t)
  | .not F => .not (orbitFormula p flip F)
  | .and F G => .and (orbitFormula p flip F) (orbitFormula p flip G)
  | .or F G => .or (orbitFormula p flip F) (orbitFormula p flip G)

theorem orbitFormula_eval (p : Relabeling 4) (flip : Bool)
    (F : Formula) (q : SixTuple) :
    (orbitFormula p flip F).eval q = F.eval (orbitTuple p flip q) := by
  induction F with
  | equal s t => simp [orbitFormula, Formula.eval, orbitPolyTerm_eval]
  | lessEq s t => simp [orbitFormula, Formula.eval, orbitPolyTerm_eval]
  | not F ih => simp [orbitFormula, Formula.eval, ih]
  | and F G ihF ihG => simp [orbitFormula, Formula.eval, ihF, ihG]
  | or F G ihF ihG => simp [orbitFormula, Formula.eval, ihF, ihG]

theorem orbitMatrix_skew (p : Relabeling 4) (flip : Bool) (q : SixTuple) :
    SkewSymmetric (orbitMatrix p flip q) := by
  have hq : SkewSymmetric (ofTuple q) :=
    ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  cases flip
  · exact relabel_skew _ p hq
  · exact reverse_skew _ (relabel_skew _ p hq)

theorem ofTuple_orbitTuple (p : Relabeling 4) (flip : Bool)
    (q : SixTuple) :
    ofTuple (orbitTuple p flip q) = orbitMatrix p flip q := by
  simpa [ofTuple, orbitTuple] using
    ofSix_reconstruct (orbitMatrix p flip q) (orbitMatrix_skew p flip q)

theorem orbitMA_iff (p : Relabeling 4) (flip : Bool)
    (q : SixTuple) :
    MutationAcyclic (ofTuple (orbitTuple p flip q)) ↔
      MutationAcyclic (ofTuple q) := by
  rw [ofTuple_orbitTuple]
  cases flip with
  | false => simpa [orbitMatrix] using MA_relabel_iff (ofTuple q) p
  | true =>
      simpa [orbitMatrix] using (MA_reverse_iff _
        (relabel_skew _ p
          (ofSix_skew (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)))).trans
        (MA_relabel_iff _ p)

def orbitFiveParameterChamberSyntax (p : Relabeling 4)
    (flip : Bool) : Formula :=
  orbitFormula p flip fiveParameterChamberSyntax

def orbitFiveParameterMASetSyntax (p : Relabeling 4)
    (flip : Bool) : Formula :=
  orbitFormula p flip fiveParameterMASetSyntax

/-- The chamber test transported under any fixed vertex permutation and
optional reversal. The premise is the already isolated structural bridge. -/
theorem orbitFiveParameterMASetSyntax_correct
    (hExist : ProperObstructionSoundness.MAHasTotalProper4)
    (p : Relabeling 4) (flip : Bool) (q : SixTuple) :
    (orbitFiveParameterMASetSyntax p flip).eval q = true ↔
      FiveParameterChamber (orbitTuple p flip q) ∧
        MutationAcyclic (ofTuple q) := by
  rw [orbitFiveParameterMASetSyntax, orbitFormula_eval,
    fiveParameterMASetSyntax_correct hExist, orbitMA_iff]

theorem orbitFiveParameterChamberSyntax_eval
    (p : Relabeling 4) (flip : Bool) (q : SixTuple) :
    (orbitFiveParameterChamberSyntax p flip).eval q = true ↔
      FiveParameterChamber (orbitTuple p flip q) := by
  rw [orbitFiveParameterChamberSyntax, orbitFormula_eval,
    fiveParameterChamberSyntax_eval]

/-- Three adjacent transpositions and three swaps with vertex 3 generate the
24 possible vertex relabelings.  The inverse maps are the same swaps. -/
def swap01 : Relabeling 4 where
  toFun i := if i = 0 then 1 else if i = 1 then 0 else i
  invFun i := if i = 0 then 1 else if i = 1 then 0 else i
  left_inv := by decide
  right_inv := by decide

def swap12 : Relabeling 4 where
  toFun i := if i = 1 then 2 else if i = 2 then 1 else i
  invFun i := if i = 1 then 2 else if i = 2 then 1 else i
  left_inv := by decide
  right_inv := by decide

def swap03 : Relabeling 4 where
  toFun i := if i = 0 then 3 else if i = 3 then 0 else i
  invFun i := if i = 0 then 3 else if i = 3 then 0 else i
  left_inv := by decide
  right_inv := by decide

def swap13 : Relabeling 4 where
  toFun i := if i = 1 then 3 else if i = 3 then 1 else i
  invFun i := if i = 1 then 3 else if i = 3 then 1 else i
  left_inv := by decide
  right_inv := by decide

def swap23 : Relabeling 4 where
  toFun i := if i = 2 then 3 else if i = 3 then 2 else i
  invFun i := if i = 2 then 3 else if i = 3 then 2 else i
  left_inv := by decide
  right_inv := by decide

def permutations012 : List (Relabeling 4) :=
  [Relabeling.identity 4, swap01, swap12,
   swap01.trans swap12, swap12.trans swap01,
   (swap01.trans swap12).trans swap01]

/-- Exactly 24 extensionally distinct relabelings. -/
def permutations4 : List (Relabeling 4) :=
  permutations012.flatMap fun s =>
    [Relabeling.identity 4, swap03, swap13, swap23].map fun t => s.trans t

private def permutationKey (p : Relabeling 4) :
    Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
  (p.toFun 0, p.toFun 1, p.toFun 2, p.toFun 3)

theorem permutations4_length : permutations4.length = 24 := by decide

theorem permutations4_keys_nodup :
    (permutations4.map permutationKey).Nodup := by decide

private theorem permutations4_keys_complete :
    ∀ a b c d : Fin 4,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (a, b, c, d) ∈ permutations4.map permutationKey := by decide

/-- Every vertex relabeling occurs in the fixed 24-element list, up to
equality of its action on vertices. -/
theorem permutations4_complete (p : Relabeling 4) :
    ∃ s ∈ permutations4, ∀ i : Fin 4, s.toFun i = p.toFun i := by
  have hne (i j : Fin 4) (hij : i ≠ j) : p.toFun i ≠ p.toFun j := by
    intro h
    exact hij (p.injective h)
  have hkey := permutations4_keys_complete
    (p.toFun 0) (p.toFun 1) (p.toFun 2) (p.toFun 3)
    (hne 0 1 (by decide)) (hne 0 2 (by decide))
    (hne 0 3 (by decide)) (hne 1 2 (by decide))
    (hne 1 3 (by decide)) (hne 2 3 (by decide))
  obtain ⟨s, hs, heq⟩ := List.mem_map.mp hkey
  refine ⟨s, hs, ?_⟩
  intro i
  have h0 : s.toFun 0 = p.toFun 0 := congrArg (fun x => x.1) heq
  have h1 : s.toFun 1 = p.toFun 1 := congrArg (fun x => x.2.1) heq
  have h2 : s.toFun 2 = p.toFun 2 := congrArg (fun x => x.2.2.1) heq
  have h3 : s.toFun 3 = p.toFun 3 := congrArg (fun x => x.2.2.2) heq
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The 48 fixed relabeling/reversal branches. -/
def chamberOrbitStates : List (Relabeling 4 × Bool) :=
  permutations4.flatMap fun p => [(p, false), (p, true)]

theorem chamberOrbitStates_length : chamberOrbitStates.length = 48 := by decide

def orbitUnionSyntax : List (Relabeling 4 × Bool) → Formula
  | [] => .equal (.const 0) (.const 1)
  | (p, flip) :: rest =>
      .or (orbitFiveParameterMASetSyntax p flip) (orbitUnionSyntax rest)

/-- A disjunction over a concrete finite list of symmetry images. -/
theorem orbitUnionSyntax_correct
    (hExist : ProperObstructionSoundness.MAHasTotalProper4)
    (states : List (Relabeling 4 × Bool)) (q : SixTuple) :
    (orbitUnionSyntax states).eval q = true ↔
      (∃ s ∈ states, FiveParameterChamber (orbitTuple s.1 s.2 q)) ∧
        MutationAcyclic (ofTuple q) := by
  induction states with
  | nil => simp [orbitUnionSyntax, Formula.eval, PolyTerm.eval]
  | cons s rest ih =>
      rcases s with ⟨p, flip⟩
      simp only [orbitUnionSyntax, Formula.eval, Bool.or_eq_true,
        orbitFiveParameterMASetSyntax_correct hExist, ih, List.mem_cons]
      constructor
      · rintro (⟨hch, hma⟩ | ⟨⟨t, ht, hch⟩, hma⟩)
        · exact ⟨⟨(p, flip), Or.inl rfl, hch⟩, hma⟩
        · exact ⟨⟨t, Or.inr ht, hch⟩, hma⟩
      · rintro ⟨⟨t, ht, hch⟩, hma⟩
        rcases ht with rfl | ht
        · exact Or.inl ⟨hch, hma⟩
        · exact Or.inr ⟨⟨t, ht, hch⟩, hma⟩

/-- A single fixed algebraic formula for all 48 transported chambers. -/
def fortyEightChamberMASetSyntax : Formula :=
  orbitUnionSyntax chamberOrbitStates

def FortyEightChamberInput (q : SixTuple) : Prop :=
  ∃ s ∈ chamberOrbitStates, FiveParameterChamber (orbitTuple s.1 s.2 q)

/-- This abstract guard quantifies over all relabelings, while the syntax
above is still one explicitly fixed 48-branch formula. -/
def FullSymmetryChamber (q : SixTuple) : Prop :=
  ∃ (p : Relabeling 4) (flip : Bool),
    FiveParameterChamber (orbitTuple p flip q)

theorem fortyEightChamberInput_iff_fullSymmetryChamber (q : SixTuple) :
    FortyEightChamberInput q ↔ FullSymmetryChamber q := by
  constructor
  · rintro ⟨⟨p, flip⟩, _, hch⟩
    exact ⟨p, flip, hch⟩
  · rintro ⟨p, flip, hch⟩
    obtain ⟨s, hs, hfun⟩ := permutations4_complete p
    have hmat : relabel (ofTuple q) s = relabel (ofTuple q) p := by
      funext i j
      simp only [relabel, hfun]
    have horbit : orbitTuple s flip q = orbitTuple p flip q := by
      simp only [orbitTuple, orbitMatrix, hmat]
    have hmem : (s, flip) ∈ chamberOrbitStates := by
      simp only [chamberOrbitStates, List.mem_flatMap]
      refine ⟨s, hs, ?_⟩
      cases flip <;> simp
    exact ⟨(s, flip), hmem, horbit ▸ hch⟩

theorem fortyEightChamberMASetSyntax_correct
    (hExist : ProperObstructionSoundness.MAHasTotalProper4)
    (q : SixTuple) :
    fortyEightChamberMASetSyntax.eval q = true ↔
      FortyEightChamberInput q ∧ MutationAcyclic (ofTuple q) :=
  orbitUnionSyntax_correct hExist chamberOrbitStates q

theorem fortyEightChamberMASetSyntax_correct_allSymmetries
    (hExist : ProperObstructionSoundness.MAHasTotalProper4)
    (q : SixTuple) :
    fortyEightChamberMASetSyntax.eval q = true ↔
      FullSymmetryChamber q ∧ MutationAcyclic (ofTuple q) := by
  rw [fortyEightChamberMASetSyntax_correct hExist,
    fortyEightChamberInput_iff_fullSymmetryChamber]

#print axioms orbitFormula_eval
#print axioms orbitMA_iff
#print axioms orbitFiveParameterMASetSyntax_correct
#print axioms permutations4_complete
#print axioms fortyEightChamberMASetSyntax_correct
#print axioms fortyEightChamberMASetSyntax_correct_allSymmetries

end Rank4Construction
