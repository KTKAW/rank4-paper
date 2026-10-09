import Rank4Round8.Reduction.FrontierBoxReach
import Rank4Round8.Arithmetic.ConeOrbitFastScan

/-!
Explicit finite coordinate equality for the two function types used by the
final classifier.  These executable definitions avoid the inherited
function-extensionality proof fields in Mathlib's default `DecidableEq`.
The module tests two actual consumer sites without modifying archived or
integrated definitions.
-/

namespace Rank4Round8.Reduction

open Rank4Formula QuiverProofs Rank4Round6.Coordinator
open Rank4Round8.Arithmetic

def explicitSixEq (q r : SixTuple) : Bool :=
  (List.finRange 6).all (fun i => decide (q i = r i))

theorem explicitSixEq_iff (q r : SixTuple) :
    explicitSixEq q r = true ↔ q = r := by
  simp only [explicitSixEq, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    exact h i (List.mem_finRange i)
  · intro h
    subst r
    intro i hi
    rfl

def explicitMatrixEq (B C : Matrix 4) : Bool :=
  (List.finRange 4).all (fun i =>
    (List.finRange 4).all (fun j => decide (B i j = C i j)))

theorem explicitMatrixEq_iff (B C : Matrix 4) :
    explicitMatrixEq B C = true ↔ B = C := by
  simp only [explicitMatrixEq, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    funext i j
    exact h i (List.mem_finRange i) j (List.mem_finRange j)
  · intro h
    subst C
    intro i hi j hj
    rfl

/-- A local replacement for the default function-valued equality instance. -/
def explicitSixDecEq : DecidableEq SixTuple := fun q r =>
  if h : explicitSixEq q r = true then
    .isTrue ((explicitSixEq_iff q r).mp h)
  else
    .isFalse (fun he => h ((explicitSixEq_iff q r).mpr he))

/-- A local replacement for the default matrix equality instance. -/
def explicitMatrixDecEq : DecidableEq (Matrix 4) := fun B C =>
  if h : explicitMatrixEq B C = true then
    .isTrue ((explicitMatrixEq_iff B C).mp h)
  else
    .isFalse (fun he => h ((explicitMatrixEq_iff B C).mpr he))

/-- The first finite-box mutation expansion with explicit matrix equality. -/
def mutationImageExplicit (B : Matrix 4) : Finset (Matrix 4) :=
  letI : DecidableEq (Matrix 4) := explicitMatrixDecEq
  (Finset.univ : Finset (Fin 4)).image (mutate B)

def univFourProbe : Finset (Fin 4) := Finset.univ
def fintypeFinFourProbe : Fintype (Fin 4) := inferInstance

def finFourListProbe : List (Fin 4) := [0, 1, 2, 3]
def finFourFinsetProbe : Finset (Fin 4) := finFourListProbe.toFinset
def natFinsetProbe : Finset Nat := ([0, 1, 2, 3] : List Nat).toFinset
def matrixSingletonProbe (B : Matrix 4) : Finset (Matrix 4) :=
  letI : DecidableEq (Matrix 4) := explicitMatrixDecEq
  {B}

def mutationListExplicit (B : Matrix 4) : Finset (Matrix 4) :=
  letI : DecidableEq (Matrix 4) := explicitMatrixDecEq
  ([mutate B 0, mutate B 1, mutate B 2, mutate B 3] : List (Matrix 4)).toFinset

def successorsExplicit (H : Nat) (B : Matrix 4) : Finset (Matrix 4) :=
  letI : DecidableEq (Matrix 4) := explicitMatrixDecEq
  ((Finset.univ : Finset (Fin 4)).image (mutate B)).filter
    (fun C => insideBox H C)

theorem successorsExplicit_eq (H : Nat) (B : Matrix 4) :
    successorsExplicit H B = successors H B := by
  ext C
  simp only [successorsExplicit, successors, Finset.mem_filter,
    Finset.mem_image]

/-- A choice-free list representation of the same one-step successors.
Duplicates are allowed; a full frontier implementation would need an
explicit list deduplication and fresh-state invariant. -/
def successorsListExplicit (H : Nat) (B : Matrix 4) : List (Matrix 4) :=
  [mutate B 0, mutate B 1, mutate B 2, mutate B 3].filter
    (fun C => insideBox H C)

theorem successorsListExplicit_mem_iff (H : Nat) (B C : Matrix 4) :
    C ∈ successorsListExplicit H B ↔ C ∈ successors H B := by
  have hvertices :
      C ∈ [mutate B 0, mutate B 1, mutate B 2, mutate B 3] ↔
        ∃ k : Fin 4, mutate B k = C := by
    constructor
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
      · exact ⟨3, h.symm⟩
    · rintro ⟨k, h⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      fin_cases k
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr h.symm))
  simp only [successorsListExplicit, List.mem_filter, successors,
    Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  simp only [hvertices]

/-- A finite arithmetic cone scan with explicit six-coordinate equality. -/
def coneScanAuxExplicit (q : SixTuple) : Nat → Cone.State → Bool
  | 0, s => explicitSixEq q (coneTupleAtState s)
  | fuel + 1, s =>
      if explicitSixEq q (coneTupleAtState s) then true
      else coneScanAuxExplicit q fuel (Cone.step 2 1 1 s)

theorem coneScanAuxExplicit_eq (q : SixTuple) (fuel : Nat)
    (s : Cone.State) :
    coneScanAuxExplicit q fuel s = coneScanAux q fuel s := by
  induction fuel generalizing s with
  | zero =>
      change explicitSixEq q (coneTupleAtState s) =
        decide (q = coneTupleAtState s)
      by_cases h : q = coneTupleAtState s
      · have he : explicitSixEq q (coneTupleAtState s) = true :=
          (explicitSixEq_iff _ _).mpr h
        rw [he]
        simp [h]
      · have he : explicitSixEq q (coneTupleAtState s) = false := by
          cases hx : explicitSixEq q (coneTupleAtState s) with
          | false => rfl
          | true => exact False.elim (h ((explicitSixEq_iff _ _).mp hx))
        simp [he, h]
  | succ fuel ih =>
      change (if explicitSixEq q (coneTupleAtState s) then true
        else coneScanAuxExplicit q fuel (Cone.step 2 1 1 s)) =
        (if q = coneTupleAtState s then true
        else coneScanAux q fuel (Cone.step 2 1 1 s))
      by_cases h : q = coneTupleAtState s
      · have he : explicitSixEq q (coneTupleAtState s) = true :=
          (explicitSixEq_iff _ _).mpr h
        simp only [he, ↓reduceIte, if_pos h]
      · have he : explicitSixEq q (coneTupleAtState s) = false := by
          cases hx : explicitSixEq q (coneTupleAtState s) with
          | false => rfl
          | true => exact False.elim (h ((explicitSixEq_iff _ _).mp hx))
        simp only [he, if_neg h]
        exact ih _

def coneOrbitShortcutFastExplicit (q : SixTuple) : Option Bool :=
  if q 0 = -2 ∧ q 1 = -1 ∧ q 3 = -1 then
    if coneScanAuxExplicit q (Nat.log2 (q 2).toNat) coneArithmeticSeed then
      some true
    else none
  else none

theorem coneOrbitShortcutFastExplicit_eq (q : SixTuple) :
    coneOrbitShortcutFastExplicit q = coneOrbitShortcutFast q := by
  simp only [coneOrbitShortcutFastExplicit, coneOrbitShortcutFast,
    coneScanAuxExplicit_eq]

#print axioms explicitSixEq
#print axioms explicitMatrixEq
#print axioms explicitSixDecEq
#print axioms explicitMatrixDecEq
#print axioms univFourProbe
#print axioms fintypeFinFourProbe
#print fintypeFinFourProbe
#print axioms finFourListProbe
#print axioms finFourFinsetProbe
#print axioms natFinsetProbe
#print axioms matrixSingletonProbe
#print axioms List.toFinset
#print axioms List.dedup
#print axioms List.Perm.dedup
#print axioms Multiset.toFinset
#print axioms Multiset.dedup
#print axioms Multiset.nodup_dedup
#print axioms mutationImageExplicit
#print axioms mutationListExplicit
#print mutationImageExplicit
#print axioms successorsExplicit
#print axioms successorsListExplicit
#print axioms insideBox
#print axioms coneScanAuxExplicit
#print axioms coneOrbitShortcutFastExplicit
#print axioms successorsExplicit_eq
#print axioms successorsListExplicit_mem_iff
#print axioms coneOrbitShortcutFastExplicit_eq

end Rank4Round8.Reduction
