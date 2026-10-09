import MA4RestartArrow20261003.RightTracedReplacement
import MA4RestartArrow20261003.GreenFamilySameColorHom
import MA4RestartArrow20261003.ActualRightSweep

/-! Construct all actual fixed-green-pivot replacements together and match
that SAME family to the exact original numerical terminal right sweep.
Only selected OLD Euler-weight inequalities and OLD same-color Hom gates
are dynamic inputs, to be derived from the original chronological Inv. -/
namespace QuiverProofs.MA4RestartArrow20261003.GreenFamilyConstruction
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceTeamBRootPositivity MAExistenceSupportChronology
open MA4RestartArrow20261003.AdjacentExceptionalFrame
open MA4RestartArrow20261003.SignedAdjacentLeftHom
open MA4RestartArrow20261003.ActualLeftSweep
open MA4RestartArrow20261003.RightFamilyFrame
open MA4RestartRightColorTraceHom
open MA4RestartArrow20261003.RightTracedReplacement
open MA4RestartArrow20261003.LeftTracedReplacement
open MA4RestartArrow20261003.GreenFamilySameColorHom
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

theorem signed_green_pivot_weight
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (D U : Matrix 4) (c : Fin 4 → Bool)
    (hD : ∀ j a, (Module.finrank K ((F a).obj (M j)) : Int) = branchSign (c j) * D a j)
    (t i : Fin 4) (hc : c t = true)
    (hEuler : pairing U (vertexDimensions F (M t)) (vertexDimensions F (M i)) =
      (Module.finrank K (M t ⟶ M i) : Int) - (Module.finrank K (Ext (M t) (M i) 1) : Int)) :
    pairing U (column D t) (column D i) = 1 * branchSign (c i) *
      ((Module.finrank K (M t ⟶ M i) : Int) - (Module.finrank K (Ext (M t) (M i) 1) : Int)) := by
  have hx : vertexDimensions F (M i) = fun a => branchSign (c i) * column D i a := by
    funext a; exact hD i a
  have hy : vertexDimensions F (M t) = fun a => branchSign (c t) * column D t a := by
    funext a; exact hD t a
  have hf : pairing U (vertexDimensions F (M t)) (vertexDimensions F (M i)) =
      branchSign (c t) * branchSign (c i) * pairing U (column D t) (column D i) := by
    rw [hy,hx]; simp only [pairing]; ring
  rw [hf,hc] at hEuler
  cases hi : c i <;> simp only [branchSign, hi, Bool.false_eq_true, ↓reduceIte,
    neg_one_mul, one_mul, mul_neg, mul_one] at hEuler ⊢ <;> omega

theorem successor_eq_add_one (j : Fin 4) (hj : j < 3) : successor j = j+1 := by
  fin_cases j <;> simp_all [successor]

theorem construct_traced_green_family
    (F : Fin 4 → C ⥤ ModuleCat.{v} K)
    (hZero : ∀ a, (F a).PreservesZeroMorphisms)
    (hLimits : ∀ a, PreservesFiniteLimits (F a))
    (hColimits : ∀ a, PreservesFiniteColimits (F a))
    (hJointEpi : ∀ {M V : C} (e : M ⟶ V), (∀ a, Epi ((F a).map e)) → Epi e)
    (hHered : ∀ T : C, HasProjectiveDimensionLT T 2)
    (hFinite : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) → (∀ a, Module.Finite K ((F a).obj Y)) →
      Module.Finite K (X ⟶ Y) ∧ Module.Finite K (Ext X Y 1))
    (U D : Matrix 4)
    (hEuler : ∀ X Y : C,
      (∀ a, Module.Finite K ((F a).obj X)) → (∀ a, Module.Finite K ((F a).obj Y)) →
      pairing U (vertexDimensions F X) (vertexDimensions F Y) =
        (Module.finrank K (X ⟶ Y) : Int) - (Module.finrank K (Ext X Y 1) : Int))
    (M : Fin 4 → C) (hM : ExceptionalFrame F M) (c : Fin 4 → Bool)
    (hD : ∀ j a, (Module.finrank K ((F a).obj (M j)) : Int) = branchSign (c j) * D a j)
    (t q : Fin 4) (htq : t ≤ q) (hc : c t = true)
    (hOldSame : ∀ i, t < i → c i = c t → ∀ f : M t ⟶ M i, f = 0)
    (hSelected : ∀ i, t < i → i ≤ q → pairing U (column D t) (column D i) ≤ 0) :
    ∃ (Q : Fin 4 → C) (g : Fin 4 → Bool),
      (∀ i, t < i → i ≤ q → RightReplacement F (M t) (M i) (Q i)) ∧
      (∀ i, t < i → i ≤ q → RightColorTrace (K := K) (M i) (M t) (Q i) (c i) (g i)) ∧
      ExceptionalFrame F (rightFamilyObjects M Q t q) ∧
      SignedDimensions F (rightFamilyObjects M Q t q) (negateColumn (rightSweep U D t q) q)
        (fun j => branchSign (rightFamilyColors c g t q j)) := by
  classical
  have hW : ∀ i, pairing U (column D t) (column D i) = 1 * branchSign (c i) *
      ((Module.finrank K (M t ⟶ M i) : Int) - (Module.finrank K (Ext (M t) (M i) 1) : Int)) := by
    intro i
    exact signed_green_pivot_weight F M D U c hD t i hc
      (hEuler _ _ (hM.finiteVertices t) (hM.finiteVertices i))
  have hExists : ∀ i, ∃ (V : C) (b : Bool), t < i ∧ i ≤ q →
      RightReplacement F (M t) (M i) V ∧ RightColorTrace (K := K) (M i) (M t) V (c i) b ∧
      (∀ a, (Module.finrank K ((F a).obj V) : Int) =
        branchSign b * (D a i - pairing U (column D t) (column D i) * D a t)) := by
    intro i
    by_cases hi : t < i ∧ i ≤ q
    · have hf := hFinite (M t) (M i) (hM.finiteVertices t) (hM.finiteVertices i)
      letI := hf.1; letI := hf.2
      have hOldHom : c i = true → ∀ f : M t ⟶ M i, f = 0 :=
        fun h => hOldSame i hi.1 (h.trans hc.symm)
      have hRed : c i = false → 0 ≤
          (Module.finrank K (M t ⟶ M i) : Int) - (Module.finrank K (Ext (M t) (M i) 1) : Int) := by
        intro h
        have hw := hW i; have hs := hSelected i hi.1 hi.2
        simp only [h, branchSign, Bool.false_eq_true, ↓reduceIte, one_mul, mul_neg, mul_one] at hw
        omega
      obtain ⟨V, b, hV, hTrace, hd⟩ := green_pivot_traced_replacement F hZero hLimits hColimits
        hJointEpi hHered M hM D c hD t i hi.1 hc hOldHom hRed
      refine ⟨V,b,fun _ => ⟨hV,hTrace,?_⟩⟩
      intro a
      rw [hW i]
      exact hd a
    · exact ⟨M i,c i,fun h => False.elim (hi h)⟩
  choose Q g hQg using hExists
  have hQ := fun i hti hiq => (hQg i ⟨hti,hiq⟩).1
  have hTrace := fun i hti hiq => (hQg i ⟨hti,hiq⟩).2.1
  refine ⟨Q,g,hQ,hTrace,right_family_exceptional_frame F M Q hM t q htq hQ,?_⟩
  intro j
  constructor
  · cases h : rightFamilyColors c g t q j <;> simp [branchSign,h]
  · intro a
    dsimp only
    by_cases hj : j = q
    · subst j
      have ho : rightFamilyObjects M Q t q q = M t := by simp [rightFamilyObjects]
      rw [ho]
      have hd := hD t a
      rw [hc] at hd
      simpa [rightFamilyColors,branchSign,negateColumn,rightSweep_entries U D t q htq] using hd
    · by_cases hji : t ≤ j ∧ j < q
      · have hp : t < successor j ∧ successor j ≤ q := by
          have hSucc : (successor j).val = j.val+1 := by
            have hj3 : j < 3 := by omega
            fin_cases j <;> simp_all [successor]
          change t.val < (successor j).val ∧ (successor j).val ≤ q.val
          rw [hSucc]
          constructor <;> omega
        have ho : rightFamilyObjects M Q t q j = Q (successor j) := by simp [rightFamilyObjects,hj,hji]
        have hcol : rightFamilyColors c g t q j = g (successor j) := by simp [rightFamilyColors,hj,hji]
        have hpred : successor j = j+1 := successor_eq_add_one j (by omega)
        rw [ho,hcol]
        simp only [negateColumn,if_neg hj,rightSweep_entries U D t q htq,if_pos hji,←hpred]
        exact (hQg _ hp).2.2 a
      · have ho : rightFamilyObjects M Q t q j = M j := by simp [rightFamilyObjects,hj,hji]
        have hcol : rightFamilyColors c g t q j = c j := by simp [rightFamilyColors,hj,hji]
        rw [ho,hcol]
        simp only [negateColumn,if_neg hj,rightSweep_entries U D t q htq,if_neg hji]
        exact hD j a

#print axioms signed_green_pivot_weight
#print axioms construct_traced_green_family
end QuiverProofs.MA4RestartArrow20261003.GreenFamilyConstruction
