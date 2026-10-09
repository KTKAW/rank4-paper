import MA4RestartArrow20261003.LeftHomMutationOldVertices
import Mathlib.Tactic.FinCases

/-! Preserve an actual ordered exceptional sequence at an adjacent left
Hom mutation. The next objects and their properties are constructed from
old pair data; this is a private categorical step, not a numerical-history
realization theorem. -/
namespace QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
set_option maxHeartbeats 0

structure ExceptionalFrame (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C) : Prop where
  rigid : ∀ a, ∀ x : Ext (M a) (M a) 1, x = 0
  scalarEnd : ∀ a, ∀ g : M a ⟶ M a, ∃ c : K, g = c • 𝟙 (M a)
  nonzeroId : ∀ a, 𝟙 (M a) ≠ 0
  finiteVertices : ∀ a b, Module.Finite K ((F b).obj (M a))
  reverseHom : ∀ a b, a < b → ∀ g : M b ⟶ M a, g = 0
  reverseExt : ∀ a b, a < b → ∀ x : Ext (M b) (M a) 1, x = 0

/-- Replace the adjacent pair (X,Y) by (Y,Q); all other objects retain
both their position and their identity. -/
def leftObjects (M : Fin 4 → C) (t : Fin 4) (Q : C) : Fin 4 → C := fun j =>
  if j = t then M (t+1) else if j = t+1 then Q else M j

/-- Both outside orthogonality laws plus the new pair's reverse law are
the exact categorical interface for one adjacent replacement. -/
theorem frame_leftObjects
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (hM : ExceptionalFrame F M) (t : Fin 4) (ht : t < 3) (Q : C)
    (hRigid : ∀ x : Ext Q Q 1, x = 0)
    (hEnd : ∀ g : Q ⟶ Q, ∃ c : K, g = c • 𝟙 Q)
    (hId : 𝟙 Q ≠ 0)
    (hFinite : ∀ a, Module.Finite K ((F a).obj Q))
    (hInternal : (∀ g : Q ⟶ M (t+1), g = 0) ∧
      (∀ x : Ext Q (M (t+1)) 1, x = 0))
    (hOutside : ∀ T : C,
      ((∀ g : M t ⟶ T, g = 0) ∧ (∀ x : Ext (M t) T 1, x = 0)) →
      ((∀ g : M (t+1) ⟶ T, g = 0) ∧ (∀ x : Ext (M (t+1)) T 1, x = 0)) →
      ((∀ g : Q ⟶ T, g = 0) ∧ (∀ x : Ext Q T 1, x = 0)))
    (hInside : ∀ T : C,
      ((∀ g : T ⟶ M t, g = 0) ∧ (∀ x : Ext T (M t) 1, x = 0)) →
      ((∀ g : T ⟶ M (t+1), g = 0) ∧ (∀ x : Ext T (M (t+1)) 1, x = 0)) →
      ((∀ g : T ⟶ Q, g = 0) ∧ (∀ x : Ext T Q 1, x = 0))) :
    ExceptionalFrame F (leftObjects M t Q) := by
  have htval : (t+1).val = t.val + 1 := by fin_cases t <;> simp_all
  have ht1 : t < t+1 := by omega
  have hAt : leftObjects M t Q t = M (t+1) := by simp [leftObjects]
  have hNext : leftObjects M t Q (t+1) = Q := by simp [leftObjects, ne_of_gt ht1]
  have hElse : ∀ a, a ≠ t → a ≠ t+1 → leftObjects M t Q a = M a := by
    intro a ha hb; simp [leftObjects, ha, hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a = t
    · rw [ha, hAt]
      exact hM.rigid (t+1)
    · by_cases hb : a = t+1
      · rw [hb, hNext]
        exact hRigid
      · rw [hElse a ha hb]
        exact hM.rigid a
  · intro a
    by_cases ha : a = t
    · rw [ha, hAt]
      exact hM.scalarEnd (t+1)
    · by_cases hb : a = t+1
      · rw [hb, hNext]
        exact hEnd
      · rw [hElse a ha hb]
        exact hM.scalarEnd a
  · intro a
    by_cases ha : a = t
    · rw [ha, hAt]
      exact hM.nonzeroId (t+1)
    · by_cases hb : a = t+1
      · rw [hb, hNext]
        exact hId
      · rw [hElse a ha hb]
        exact hM.nonzeroId a
  · intro a b
    by_cases ha : a = t
    · rw [ha, hAt]
      exact hM.finiteVertices (t+1) b
    · by_cases hb : a = t+1
      · rw [hb, hNext]
        exact hFinite b
      · rw [hElse a ha hb]
        exact hM.finiteVertices a b
  · intro a b hab
    by_cases ha : a = t
    · subst a
      have hb : b ≠ t := by omega
      by_cases hb1 : b = t+1
      · rw [hb1, hNext, hAt]
        exact hInternal.1
      · have htb : t+1 < b := by omega
        rw [hElse b hb hb1, hAt]
        exact hM.reverseHom (t+1) b htb
    · by_cases ha1 : a = t+1
      · subst a
        have hb : b ≠ t := by omega
        have hb1 : b ≠ t+1 := by omega
        have htb : t < b := by omega
        have h := hInside (M b)
          ⟨hM.reverseHom t b htb, hM.reverseExt t b htb⟩
          ⟨hM.reverseHom (t+1) b hab, hM.reverseExt (t+1) b hab⟩
        rw [hElse b hb hb1, hNext]
        exact h.1
      · by_cases hb : b = t
        · subst b
          have hat : a < t+1 := by omega
          rw [hAt, hElse a ha ha1]
          exact hM.reverseHom a (t+1) hat
        · by_cases hb1 : b = t+1
          · subst b
            have hat : a < t := by omega
            have h := hOutside (M a)
              ⟨hM.reverseHom a t hat, hM.reverseExt a t hat⟩
              ⟨hM.reverseHom a (t+1) hab, hM.reverseExt a (t+1) hab⟩
            rw [hNext, hElse a ha ha1]
            exact h.1
          · rw [hElse b hb hb1, hElse a ha ha1]
            exact hM.reverseHom a b hab
  · intro a b hab
    by_cases ha : a = t
    · subst a
      have hb : b ≠ t := by omega
      by_cases hb1 : b = t+1
      · rw [hb1, hNext, hAt]
        exact hInternal.2
      · have htb : t+1 < b := by omega
        rw [hElse b hb hb1, hAt]
        exact hM.reverseExt (t+1) b htb
    · by_cases ha1 : a = t+1
      · subst a
        have hb : b ≠ t := by omega
        have hb1 : b ≠ t+1 := by omega
        have htb : t < b := by omega
        have h := hInside (M b)
          ⟨hM.reverseHom t b htb, hM.reverseExt t b htb⟩
          ⟨hM.reverseHom (t+1) b hab, hM.reverseExt (t+1) b hab⟩
        rw [hElse b hb hb1, hNext]
        exact h.2
      · by_cases hb : b = t
        · subst b
          have hat : a < t+1 := by omega
          rw [hAt, hElse a ha ha1]
          exact hM.reverseExt a (t+1) hat
        · by_cases hb1 : b = t+1
          · subst b
            have hat : a < t := by omega
            have h := hOutside (M a)
              ⟨hM.reverseHom a t hat, hM.reverseExt a t hat⟩
              ⟨hM.reverseHom a (t+1) hab, hM.reverseExt a (t+1) hab⟩
            rw [hNext, hElse a ha ha1]
            exact h.2
          · rw [hElse b hb hb1, hElse a ha ha1]
            exact hM.reverseExt a b hab

open QuiverProofs.MA4RestartArrow20261003.LeftHomMutationOldVertices

/-- Construct and preserve the whole actual ordered frame on a left Hom
step. Every future frame field is a conclusion, including all finite vertices.
The forward Ext-zero branch is explicit even for n=0. -/
theorem left_hom_adjacent_frame
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (M : Fin 4 → C) (hM : ExceptionalFrame F M)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (t : Fin 4) (ht : t < 3) (n : ℕ)
    [HasBiproduct (fun _ : Fin n => M (t+1))]
    (f : Module.Basis (Fin n) K (M t ⟶ M (t+1)))
    (hForward : ∀ x : Ext (M t) (M (t+1)) 1, x = 0)
    (dX dY : Fin 4 → Int)
    (hDimX : ∀ a, (Module.finrank K ((F a).obj (M t)) : Int) = dX a)
    (hDimY : ∀ a, (Module.finrank K ((F a).obj (M (t+1))) : Int) = dY a) :
    let e := biproduct.lift (f := fun _ : Fin n => M (t+1)) (fun j => f j)
    let δ := fun a => dX a - (n : Int) * dY a
    ∃ Q : C,
      ((Mono e ∧ ¬ Epi e ∧ Q = cokernel e) ∨
       (Epi e ∧ ¬ Mono e ∧ Q = kernel e)) ∧
      ExceptionalFrame F (leftObjects M t Q) ∧
      (∀ a, (Module.finrank K ((F a).obj Q) : Int) =
        if (∀ b, 0 ≤ δ b) then δ a else -δ a) ∧
      (∃ a, 0 < Module.finrank K ((F a).obj Q)) := by
  have ht1 : t < t+1 := by fin_cases t <;> simp_all
  obtain ⟨Q, hBranch, hHom, hExt, hRigid, hEnd, hId, _hLocal, _hFE, _hDE,
    hFinite, hDim, hPos, hOut, hIn⟩ :=
    left_hom_mutation_from_old_vertices (M t) (M (t+1)) n f hHered
      (hM.reverseHom t (t+1) ht1) (hM.reverseExt t (t+1) ht1) hForward
      (hM.rigid t) (hM.rigid (t+1)) (hM.nonzeroId t)
      (hM.scalarEnd t) (hM.scalarEnd (t+1)) F hZero hLimits hColimits hJointEpi
      (hM.finiteVertices t) (hM.finiteVertices (t+1)) dX dY hDimX hDimY
  exact ⟨Q, hBranch, frame_leftObjects F M hM t ht Q hRigid hEnd hId hFinite
    ⟨hHom, hExt⟩ hOut hIn, hDim, hPos⟩

#print axioms frame_leftObjects
#print axioms left_hom_adjacent_frame
end QuiverProofs.MA4RestartArrow20261003.AdjacentExceptionalFrame
