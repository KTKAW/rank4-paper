import Rank4Round8.Arithmetic.ConeOrbitShortcut

/-!
A single-pass arithmetic scan of the cone recurrence. The prior list-based
shortcut recomputed `Cone.orbit` from its seed for every candidate. This
implementation carries one state forward and stops at the first match.
-/

namespace Rank4Round8.Arithmetic

open QuiverProofs Rank4Formula Rank4Round3

def coneTupleAtState (s : Cone.State) : SixTuple :=
  upperTuple (Cone.quiver 2 1 1 s)

theorem coneTupleAtState_orbit (n : Nat) :
    coneTupleAtState (coneArithmeticState n) = coneArithmeticTuple n := rfl

theorem coneArithmeticState_succ (n : Nat) :
    Cone.step 2 1 1 (coneArithmeticState n) =
      coneArithmeticState (n + 1) := rfl

/-- Scans `fuel+1` consecutive arithmetic states, with an early match.
    The only state update is the fixed integer-linear `Cone.step`. -/
def coneScanAux (q : SixTuple) : Nat → Cone.State → Bool
  | 0, s => decide (q = coneTupleAtState s)
  | fuel + 1, s =>
      if q = coneTupleAtState s then true
      else coneScanAux q fuel (Cone.step 2 1 1 s)

/-- A cost model following exactly the branches of `coneScanAux`: the number
    of candidate states inspected, including the final state. -/
def coneScanChecks (q : SixTuple) : Nat → Cone.State → Nat
  | 0, _ => 1
  | fuel + 1, s =>
      if q = coneTupleAtState s then 1
      else 1 + coneScanChecks q fuel (Cone.step 2 1 1 s)

theorem coneScanChecks_le (q : SixTuple) (fuel : Nat) :
    ∀ s : Cone.State, coneScanChecks q fuel s ≤ fuel + 1 := by
  induction fuel with
  | zero => intro s; simp [coneScanChecks]
  | succ fuel ih =>
      intro s
      by_cases h : q = coneTupleAtState s
      · simp [coneScanChecks, h]
      · have hh := ih (Cone.step 2 1 1 s)
        simp only [coneScanChecks, h, ↓reduceIte]
        omega

/-- Number of integer-linear state updates in the same branching scan. -/
def coneScanUpdates (q : SixTuple) : Nat → Cone.State → Nat
  | 0, _ => 0
  | fuel + 1, s =>
      if q = coneTupleAtState s then 0
      else 1 + coneScanUpdates q fuel (Cone.step 2 1 1 s)

theorem coneScanUpdates_le (q : SixTuple) (fuel : Nat) :
    ∀ s : Cone.State, coneScanUpdates q fuel s ≤ fuel := by
  induction fuel with
  | zero => intro s; simp [coneScanUpdates]
  | succ fuel ih =>
      intro s
      by_cases h : q = coneTupleAtState s
      · simp [coneScanUpdates, h]
      · have hh := ih (Cone.step 2 1 1 s)
        simp only [coneScanUpdates, h, ↓reduceIte]
        omega

theorem coneScanAux_spec (q : SixTuple) (fuel : Nat) :
    ∀ n : Nat, coneScanAux q fuel (coneArithmeticState n) = true ↔
      ∃ i : Nat, i ≤ fuel ∧ q = coneArithmeticTuple (n + i) := by
  induction fuel with
  | zero =>
      intro n
      simp [coneScanAux, coneTupleAtState_orbit]
  | succ fuel ih =>
      intro n
      by_cases h : q = coneArithmeticTuple n
      · simp [coneScanAux, coneTupleAtState_orbit, h]
        exact ⟨0, by omega, by simpa using h⟩
      · simp only [coneScanAux, coneTupleAtState_orbit, h, ↓reduceIte,
          coneArithmeticState_succ, ih (n + 1)]
        constructor
        · rintro ⟨i, hi, hqi⟩
          refine ⟨i + 1, by omega, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hqi
        · rintro ⟨i, hi, hqi⟩
          cases i with
          | zero =>
              simp only [Nat.add_zero] at hqi
              exact False.elim (h hqi)
          | succ i =>
              refine ⟨i, by omega, ?_⟩
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hqi

/-- The optimized zero-mutation recognizer. The fixed-coordinate guard avoids
    recurrence work for most inputs. -/
def coneOrbitShortcutFast (q : SixTuple) : Option Bool :=
  if q 0 = -2 ∧ q 1 = -1 ∧ q 3 = -1 then
    if coneScanAux q (Nat.log2 (q 2).toNat) coneArithmeticSeed then
      some true
    else none
  else none

theorem coneOrbitShortcutFast_arithmetic_cost (q : SixTuple) :
    coneScanChecks q (Nat.log2 (q 2).toNat) coneArithmeticSeed ≤
        Nat.log2 (q 2).toNat + 1 ∧
      coneScanUpdates q (Nat.log2 (q 2).toNat) coneArithmeticSeed ≤
        Nat.log2 (q 2).toNat :=
  ⟨coneScanChecks_le q _ _, coneScanUpdates_le q _ _⟩

theorem coneOrbitShortcutFast_eq_reference (q : SixTuple) :
    coneOrbitShortcutFast q = coneOrbitShortcut q := by
  by_cases hg : q 0 = -2 ∧ q 1 = -1 ∧ q 3 = -1
  · simp only [coneOrbitShortcutFast, coneOrbitShortcut, hg]
    have hs := coneScanAux_spec q (Nat.log2 (q 2).toNat) 0
    have hs' : coneScanAux q (Nat.log2 (q 2).toNat) coneArithmeticSeed = true ↔
        ∃ i : Nat, i ≤ Nat.log2 (q 2).toNat ∧ q = coneArithmeticTuple i := by
      simpa only [coneArithmeticState, Cone.orbit, Nat.zero_add] using hs
    have hm : (coneScanAux q (Nat.log2 (q 2).toNat) coneArithmeticSeed = true) ↔
        q ∈ (List.range (Nat.log2 (q 2).toNat + 1)).map coneArithmeticTuple := by
      rw [hs']
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, hqi⟩
        exact ⟨i, by omega, hqi.symm⟩
      · rintro ⟨i, hi, hqi⟩
        exact ⟨i, by omega, hqi.symm⟩
    by_cases h : coneScanAux q (Nat.log2 (q 2).toNat) coneArithmeticSeed = true
    · rw [if_pos h, if_pos (hm.mp h)]
    · rw [if_neg h, if_neg (fun hmem => h (hm.mpr hmem))]
  · simp [coneOrbitShortcutFast, coneOrbitShortcut, hg]

theorem coneOrbitShortcutFast_spec (q : SixTuple) (b : Bool)
    (h : coneOrbitShortcutFast q = some b) :
    b = true ↔ MutationAcyclic (ofTuple q) := by
  rw [coneOrbitShortcutFast_eq_reference] at h
  exact coneOrbitShortcut_spec q b h

theorem coneOrbitShortcutFast_complete (n : Nat) :
    coneOrbitShortcutFast (coneArithmeticTuple n) = some true := by
  rw [coneOrbitShortcutFast_eq_reference]
  exact coneOrbitShortcut_complete n

theorem coneOrbitShortcutFast_unbounded_acyclic_depth (r : Nat) :
    ∃ q : SixTuple, coneOrbitShortcutFast q = some true ∧
      ∀ w : List (Fin 4), w.length ≤ r →
        ¬ Acyclic (applyWord (ofTuple q) w) := by
  obtain ⟨q, hq, hd⟩ := coneOrbitShortcut_unbounded_acyclic_depth r
  exact ⟨q, by rw [coneOrbitShortcutFast_eq_reference]; exact hq, hd⟩

#print axioms coneScanAux_spec
#print axioms coneOrbitShortcutFast_arithmetic_cost
#print axioms coneOrbitShortcutFast_eq_reference
#print axioms coneOrbitShortcutFast_spec
#print axioms coneOrbitShortcutFast_complete
#print axioms coneOrbitShortcutFast_unbounded_acyclic_depth

end Rank4Round8.Arithmetic
