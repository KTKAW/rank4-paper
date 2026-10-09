import Rank4CoordinatorR2.PartialStage
import Rank4Round2.KleinChecker

/-! Adds automatic recognition of the reviewed unrestricted six-parameter
Klein region to the sound partial executable stage. Unknown remains unknown;
this is not an all-input classifier or a negative coverage theorem. -/
namespace Rank4CoordinatorR2.PartialStageKlein
open QuiverProofs Rank4C7A41E

inductive NegativeEvidence where
  | klein
  | previous (c : Rank4CoordinatorR2.NegativeEvidence)

def verifyNegative (Q : Rank4Input) : NegativeEvidence → Bool
  | .klein => Rank4Round2.KleinChecker.check Q.val
  | .previous c => Rank4CoordinatorR2.verifyNegative Q c

theorem verifyNegative_sound (Q : Rank4Input) (c : NegativeEvidence)
    (h : verifyNegative Q c=true) : ¬MutationAcyclic Q.val := by
  cases c with
  | klein => exact Rank4Round2.KleinChecker.check_sound Q.val Q.property h
  | previous c => exact Rank4CoordinatorR2.verifyNegative_sound Q c h

inductive Outcome where
  | ma (word : List (Fin 4))
  | nma (evidence : NegativeEvidence)
  | unknown

def liftPrevious : Rank4CoordinatorR2.Outcome → Outcome
  | .ma w => .ma w
  | .nma e => .nma (.previous e)
  | .unknown => .unknown

def classifyStage (Q : Rank4Input) (depth : Nat)
    (candidates : List Rank4CoordinatorR2.NegativeEvidence) : Outcome :=
  if Rank4Round2.KleinChecker.check Q.val then .nma .klein
  else liftPrevious (Rank4CoordinatorR2.classifyStage Q depth candidates)

def Outcome.Sound (Q : Rank4Input) : Outcome → Prop
  | .ma w => Acyclic (applyWord Q.val w)
  | .nma e => verifyNegative Q e=true ∧ ¬MutationAcyclic Q.val
  | .unknown => True

theorem classifyStage_sound (Q : Rank4Input) (depth : Nat)
    (candidates : List Rank4CoordinatorR2.NegativeEvidence) :
    Outcome.Sound Q (classifyStage Q depth candidates) := by
  cases hk : Rank4Round2.KleinChecker.check Q.val with
  | true =>
    simp only [classifyStage,hk,↓reduceIte,Outcome.Sound,verifyNegative]
    exact ⟨by trivial,Rank4Round2.KleinChecker.check_sound Q.val Q.property hk⟩
  | false =>
    have hs := Rank4CoordinatorR2.classifyStage_sound Q depth candidates
    cases hp : Rank4CoordinatorR2.classifyStage Q depth candidates with
    | ma w => simpa only [classifyStage,hk,Bool.false_eq_true,↓reduceIte,
        hp,liftPrevious,Outcome.Sound,Rank4CoordinatorR2.Outcome.Sound] using hs
    | nma e => simpa only [classifyStage,hk,Bool.false_eq_true,↓reduceIte,
        hp,liftPrevious,Outcome.Sound,verifyNegative,Rank4CoordinatorR2.Outcome.Sound] using hs
    | unknown => simp only [classifyStage,hk,Bool.false_eq_true,↓reduceIte,hp,liftPrevious,Outcome.Sound]

theorem classifyStage_unknown_excludes_short_words (Q : Rank4Input) (depth : Nat)
    (candidates : List Rank4CoordinatorR2.NegativeEvidence)
    (h : classifyStage Q depth candidates=.unknown) :
    ∀ w,w.length≤depth → ¬Acyclic (applyWord Q.val w) := by
  have hp : Rank4CoordinatorR2.classifyStage Q depth candidates=.unknown := by
    cases hk : Rank4Round2.KleinChecker.check Q.val with
    | true => simp [classifyStage,hk] at h
    | false =>
      cases ho : Rank4CoordinatorR2.classifyStage Q depth candidates <;>
        simp [classifyStage,hk,ho,liftPrevious] at h ⊢
  exact Rank4CoordinatorR2.classifyStage_unknown_excludes_short_words Q depth candidates hp

theorem classifyStage_recognized (Q : Rank4Input) (depth : Nat)
    (candidates : List Rank4CoordinatorR2.NegativeEvidence)
    (h : Rank4Round2.KleinChecker.check Q.val=true) :
    classifyStage Q depth candidates=.nma .klein := by
  simp only [classifyStage,h,↓reduceIte]

def outcomeTag : Outcome → Nat
  | .ma _ => 0 | .nma _ => 1 | .unknown => 2

#eval outcomeTag (classifyStage (ofSixInput 2 2 (-2) 2 (-2) 14) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 2 1000000 (-2) 2 (-2) 2000010) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 2 2 (-2) 2 (-2) 13) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 2 1000003 (-1) 1 (-1) 1000006) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 0 1 (-1999998) 2 (-1000000) 1999999) 0 [])
#eval outcomeTag (classifyStage (ofSixInput 0 1 0 1 0 1) 0 [])
#print axioms classifyStage
#print axioms classifyStage_sound
#print axioms classifyStage_unknown_excludes_short_words
end Rank4CoordinatorR2.PartialStageKlein
