import Rank4StructureRound2.PFamily
import Rank4StructureRound2.RFamily
import Rank4C7A41E.BoundDecision

/-! Executable recognition of two uniformly proved unbounded NMA families,
including an actual word, permutation and optional reversal in the evidence.
This negative certificate language is sound; global coverage is not claimed.
-/
namespace Rank4CoordinatorR2
open QuiverProofs Rank4C7A41E

inductive NmaFamily where
  | peak
  | zeroUnit

def PeakPattern (B : Matrix 4) : Prop :=
  B 0 1=2 ∧ 1≤B 0 2 ∧ B 0 3 = -1 ∧ B 1 2=1 ∧ B 1 3 = -1 ∧
    B 2 3=B 0 2+3

def ZeroUnitPattern (B : Matrix 4) : Prop :=
  B 0 1=0 ∧ B 0 2=1 ∧ 2≤ -B 1 3 ∧ B 0 3=2*B 1 3+2 ∧ B 1 2=2 ∧
    B 2 3= -2*B 1 3-1

instance (B : Matrix 4) : Decidable (PeakPattern B) := by
  unfold PeakPattern; infer_instance
instance (B : Matrix 4) : Decidable (ZeroUnitPattern B) := by
  unfold ZeroUnitPattern; infer_instance

def checkFamily (B : Matrix 4) : NmaFamily → Bool
  | .peak => decide (PeakPattern B)
  | .zeroUnit => decide (ZeroUnitPattern B)

theorem checkFamily_sound (B : Matrix 4) (hB : SkewSymmetric B) (family : NmaFamily)
    (h : checkFamily B family=true) : ¬ MutationAcyclic B := by
  cases family with
  | peak =>
    have hp : PeakPattern B := by simpa only [checkFamily,decide_eq_true_eq] using h
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
    have hrec := ofSix_reconstruct B hB
    rw [ha,hc,hd,he,hf] at hrec
    rw [← hrec]
    exact Rank4StructureRound2.PFamily.all_b_NMA (B 0 2) hb
  | zeroUnit =>
    have hp : ZeroUnitPattern B := by simpa only [checkFamily,decide_eq_true_eq] using h
    obtain ⟨ha,hb,hm,hc,hd,hf⟩ := hp
    have hrec := ofSix_reconstruct B hB
    have hc' : B 0 3= -(2*(-B 1 3)-2) := by omega
    have hf' : B 2 3=2*(-B 1 3)-1 := by omega
    rw [ha,hb,hc',hd,hf'] at hrec
    have he : B 1 3= -(-B 1 3) := by omega
    conv at hrec => lhs; arg 5; rw [he]
    rw [← hrec]
    exact Rank4StructureRound2.RFamily.all_m_NMA (-B 1 3) hm

structure FamilyCertificate where
  family : NmaFamily
  entry : List (Fin 4)
  permutation : Fin 24
  reversed : Bool

def familyEndpoint (Q : Rank4Input) (c : FamilyCertificate) : Matrix 4 :=
  let C := relabel (applyWord Q.val c.entry) (Census.permutation c.permutation)
  if c.reversed then reverse C else C

def checkFamilyCertificate (Q : Rank4Input) (c : FamilyCertificate) : Bool :=
  checkFamily (familyEndpoint Q c) c.family

theorem familyEndpoint_skew (Q : Rank4Input) (c : FamilyCertificate) :
    SkewSymmetric (familyEndpoint Q c) := by
  have hC := relabel_skew _ (Census.permutation c.permutation)
    (word_preserves_skew Q.val c.entry Q.property)
  unfold familyEndpoint
  split
  · exact reverse_skew _ hC
  · exact hC

theorem familyEndpoint_MA_iff (Q : Rank4Input) (c : FamilyCertificate) :
    MutationAcyclic (familyEndpoint Q c) ↔ MutationAcyclic Q.val := by
  have hC := relabel_skew _ (Census.permutation c.permutation)
    (word_preserves_skew Q.val c.entry Q.property)
  unfold familyEndpoint
  split
  · exact (MA_reverse_iff _ hC).trans
      ((MA_relabel_iff _ _).trans (mutationAcyclic_word_iff _ _))
  · exact (MA_relabel_iff _ _).trans (mutationAcyclic_word_iff _ _)

theorem checkFamilyCertificate_sound (Q : Rank4Input) (c : FamilyCertificate)
    (h : checkFamilyCertificate Q c=true) : ¬ MutationAcyclic Q.val := by
  have hn := checkFamily_sound (familyEndpoint Q c) (familyEndpoint_skew Q c) c.family h
  exact fun hma => hn ((familyEndpoint_MA_iff Q c).mpr hma)

example : checkFamily (ofSix 2 1000003 (-1) 1 (-1) 1000006) .peak=true := by decide
example : checkFamily (ofSix 2 1000003 (-1) 1 (-1) 1000007) .peak=false := by decide
example : checkFamily (ofSix 0 1 (-1999998) 2 (-1000000) 1999999) .zeroUnit=true := by decide
example : checkFamily (ofSix 0 1 (-1999998) 3 (-1000000) 1999999) .zeroUnit=false := by decide

#print axioms checkFamily
#print axioms checkFamilyCertificate
#print axioms checkFamily_sound
#print axioms checkFamilyCertificate_sound
end Rank4CoordinatorR2
