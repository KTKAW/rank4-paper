import Rank4CoordinatorR2.FamilyChecker
import Rank4C7A41E.PartialClassifier

/-! Finite, explicitly partial classification with the two reviewed uniform
families recognized automatically before positive search. Every definitive
outcome carries executable evidence. Unknown remains unknown. -/
namespace Rank4CoordinatorR2
open QuiverProofs Rank4C7A41E

inductive NegativeEvidence where
  | directFamily (family : NmaFamily)
  | family (c : FamilyCertificate)
  | existing (c : Rank4C7A41E.NegativeEvidence)

def verifyNegative (Q : Rank4Input) : NegativeEvidence → Bool
  | .directFamily family => checkFamily Q.val family
  | .family c => checkFamilyCertificate Q c
  | .existing c => Rank4C7A41E.verifyNegative Q c

theorem verifyNegative_sound (Q : Rank4Input) (c : NegativeEvidence)
    (h : verifyNegative Q c=true) : ¬MutationAcyclic Q.val := by
  cases c with
  | directFamily family => exact checkFamily_sound Q.val Q.property family h
  | family c => exact checkFamilyCertificate_sound Q c h
  | existing c => exact Rank4C7A41E.verifyNegative_sound Q c h

inductive Outcome where
  | ma (word : List (Fin 4))
  | nma (evidence : NegativeEvidence)
  | unknown

def automaticFamilies : List NegativeEvidence :=
  [.directFamily .peak,.directFamily .zeroUnit]

def classifyStage (Q : Rank4Input) (depth : Nat) (negatives : List NegativeEvidence) : Outcome :=
  match CertificateSearch.searchStage (verifyNegative Q) (automaticFamilies++negatives) with
  | some c => .nma c
  | none => match findPositive Q depth with
    | some w => .ma w
    | none => .unknown

def Outcome.Sound (Q : Rank4Input) : Outcome → Prop
  | .ma w => Acyclic (applyWord Q.val w)
  | .nma c => verifyNegative Q c=true ∧ ¬MutationAcyclic Q.val
  | .unknown => True

theorem classifyStage_sound (Q : Rank4Input) (depth : Nat)
    (negatives : List NegativeEvidence) : Outcome.Sound Q (classifyStage Q depth negatives) := by
  cases hn : CertificateSearch.searchStage (verifyNegative Q) (automaticFamilies++negatives) with
  | some c =>
    have hc := (CertificateSearch.searchStage_some_accepted (verifyNegative Q)
      (automaticFamilies++negatives) c hn).2
    simpa only [classifyStage,hn,Outcome.Sound] using ⟨hc,verifyNegative_sound Q c hc⟩
  | none =>
    cases hp : findPositive Q depth with
    | some w =>
      simpa only [classifyStage,hn,hp,Outcome.Sound] using (findPositive_some Q depth w hp).2
    | none => simp only [classifyStage,hn,hp,Outcome.Sound]

theorem classifyStage_unknown_excludes_short_words (Q : Rank4Input) (depth : Nat)
    (negatives : List NegativeEvidence) (h : classifyStage Q depth negatives=.unknown) :
    ∀ w, w.length≤depth → ¬Acyclic (applyWord Q.val w) := by
  have hp : findPositive Q depth=none := by
    cases hn : CertificateSearch.searchStage (verifyNegative Q) (automaticFamilies++negatives) with
    | some c => simp [classifyStage,hn] at h
    | none =>
      cases hp : findPositive Q depth with
      | some w => simp [classifyStage,hn,hp] at h
      | none => rfl
  exact (findPositive_none_iff Q depth).mp hp

def outcomeTag : Outcome → Nat
  | .ma _ => 0
  | .nma _ => 1
  | .unknown => 2

theorem classifyStage_P (b : Int) (hb : 1≤b) (depth : Nat)
    (negatives : List NegativeEvidence) :
    classifyStage (ofSixInput 2 b (-1) 1 (-1) (b+3)) depth negatives=
      .nma (.directFamily .peak) := by
  have hc : checkFamily (ofSix 2 b (-1) 1 (-1) (b+3)) .peak=true := by
    rw [checkFamily,decide_eq_true_eq]
    simp [PeakPattern,ofSix,hb]
  simp only [classifyStage,automaticFamilies,List.cons_append,List.nil_append,
    CertificateSearch.searchStage,verifyNegative,ofSixInput,hc,↓reduceIte]

theorem classifyStage_R (m : Int) (hm : 2≤m) (depth : Nat)
    (negatives : List NegativeEvidence) :
    classifyStage (ofSixInput 0 1 (-(2*m-2)) 2 (-m) (2*m-1)) depth negatives=
      .nma (.directFamily .zeroUnit) := by
  have hp : checkFamily (ofSix 0 1 (-(2*m-2)) 2 (-m) (2*m-1)) .peak=false := by
    simp [checkFamily,PeakPattern,ofSix]
  have hc : checkFamily (ofSix 0 1 (-(2*m-2)) 2 (-m) (2*m-1)) .zeroUnit=true := by
    rw [checkFamily,decide_eq_true_eq]
    simp [ZeroUnitPattern,ofSix]
    omega
  simp [classifyStage,automaticFamilies,CertificateSearch.searchStage,
    verifyNegative,ofSixInput,hp,hc]

#eval outcomeTag (classifyStage (ofSixInput 2 1000003 (-1) 1 (-1) 1000006) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 0 1 (-1999998) 2 (-1000000) 1999999) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 0 1 0 1 0 1) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 2 1000003 (-1) 1 (-1) 1000007) 0 [])
#print axioms classifyStage
#print axioms verifyNegative_sound
#print axioms classifyStage_sound
#print axioms classifyStage_P
#print axioms classifyStage_R
end Rank4CoordinatorR2
