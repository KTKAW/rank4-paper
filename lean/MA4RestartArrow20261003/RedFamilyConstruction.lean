import MA4RestartArrow20261003.LeftTracedReplacement
import MA4RestartArrow20261003.RedFamilySameColorHom
import MA4RestartArrow20261003.ActualFrameChronology

/-! Construct all actual fixed-red-pivot replacements together and match
that SAME family to the exact original numerical terminal left sweep.
Only selected OLD Euler-weight inequalities and OLD same-color Hom gates
are dynamic inputs, to be derived from the original chronological Inv. -/
namespace QuiverProofs.MA4RestartArrow20261003.RedFamilyConstruction
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open QuiverProofs MAExistenceLiterature MAExistenceTeamBRootPositivity MAExistenceSupportChronology
open MA4RestartArrow20261003.AdjacentExceptionalFrame
open MA4RestartArrow20261003.SignedAdjacentLeftHom
open MA4RestartArrow20261003.ActualLeftSweep
open MA4RestartArrow20261003.LeftFamilyFrame
open MA4RestartArrow20261003.LeftColorTraceHom
open MA4RestartArrow20261003.LeftTracedReplacement
open MA4RestartArrow20261003.RedFamilySameColorHom
universe w v u z
variable {K : Type w} [Field K] {C : Type u}
  [Category.{v} C] [Abelian C] [Linear K C] [HasExt.{z} C]
  [EnoughProjectives C] [HasFiniteBiproducts C]
set_option maxHeartbeats 0

theorem signed_red_pivot_weight
    (F : Fin 4 → C ⥤ ModuleCat.{v} K) (M : Fin 4 → C)
    (D U : Matrix 4) (c : Fin 4 → Bool)
    (hD : ∀ j a, (Module.finrank K ((F a).obj (M j)) : Int) = branchSign (c j) * D a j)
    (i t : Fin 4) (hc : c t = false)
    (hEuler : pairing U (vertexDimensions F (M i)) (vertexDimensions F (M t)) =
      (Module.finrank K (M i ⟶ M t) : Int) - (Module.finrank K (Ext (M i) (M t) 1) : Int)) :
    pairing U (column D i) (column D t) = branchSign (c i) * (-1) *
      ((Module.finrank K (M i ⟶ M t) : Int) - (Module.finrank K (Ext (M i) (M t) 1) : Int)) := by
  have hx : vertexDimensions F (M i) = fun a => branchSign (c i) * column D i a := by
    funext a; exact hD i a
  have hy : vertexDimensions F (M t) = fun a => branchSign (c t) * column D t a := by
    funext a; exact hD t a
  have hf : pairing U (vertexDimensions F (M i)) (vertexDimensions F (M t)) =
      branchSign (c i) * branchSign (c t) * pairing U (column D i) (column D t) := by
    rw [hx,hy]; simp only [pairing]; ring
  rw [hf,hc] at hEuler
  cases hi : c i <;> simp only [branchSign, hi, Bool.false_eq_true, ↓reduceIte,
    neg_one_mul, one_mul, mul_neg, mul_one] at hEuler ⊢ <;> omega

theorem predecessor_eq_sub_one (j : Fin 4) (hj : 0 < j) : predecessor j = j-1 := by
  fin_cases j <;> simp_all [predecessor]

theorem construct_traced_red_family
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
    (t q : Fin 4) (hqt : q ≤ t) (hc : c t = false)
    (hOldSame : ∀ i, i < t → c i = c t → ∀ f : M i ⟶ M t, f = 0)
    (hSelected : ∀ i, q ≤ i → i < t → pairing U (column D i) (column D t) ≤ 0) :
    ∃ (Q : Fin 4 → C) (g : Fin 4 → Bool),
      (∀ i, q ≤ i → i < t → LeftReplacement F (M i) (M t) (Q i)) ∧
      (∀ i, q ≤ i → i < t → LeftColorTrace (K := K) (M i) (M t) (Q i) (c i) (g i)) ∧
      ExceptionalFrame F (familyObjects M Q t q) ∧
      SignedDimensions F (familyObjects M Q t q) (negateColumn (leftSweep U D t q) q)
        (fun j => branchSign (familyColors c g t q j)) := by
  classical
  have hW : ∀ i, pairing U (column D i) (column D t) = branchSign (c i) * (-1) *
      ((Module.finrank K (M i ⟶ M t) : Int) - (Module.finrank K (Ext (M i) (M t) 1) : Int)) := by
    intro i
    exact signed_red_pivot_weight F M D U c hD i t hc
      (hEuler _ _ (hM.finiteVertices i) (hM.finiteVertices t))
  have hExists : ∀ i, ∃ (V : C) (b : Bool), q ≤ i ∧ i < t →
      LeftReplacement F (M i) (M t) V ∧ LeftColorTrace (K := K) (M i) (M t) V (c i) b ∧
      (∀ a, (Module.finrank K ((F a).obj V) : Int) =
        branchSign b * (D a i - pairing U (column D i) (column D t) * D a t)) := by
    intro i
    by_cases hi : q ≤ i ∧ i < t
    · have hf := hFinite (M i) (M t) (hM.finiteVertices i) (hM.finiteVertices t)
      letI := hf.1; letI := hf.2
      have hOldHom : c i = false → ∀ f : M i ⟶ M t, f = 0 :=
        fun h => hOldSame i hi.2 (h.trans hc.symm)
      have hGreen : c i = true → 0 ≤
          (Module.finrank K (M i ⟶ M t) : Int) - (Module.finrank K (Ext (M i) (M t) 1) : Int) := by
        intro h
        have hw := hW i; have hs := hSelected i hi.1 hi.2
        simp only [h, branchSign, ↓reduceIte, one_mul, neg_one_mul] at hw
        omega
      obtain ⟨V, b, hV, hTrace, hd⟩ := red_pivot_traced_replacement F hZero hLimits hColimits
        hJointEpi hHered M hM D c hD i t hi.2 hc hOldHom hGreen
      refine ⟨V,b,fun _ => ⟨hV,hTrace,?_⟩⟩
      intro a
      rw [hW i]
      exact hd a
    · exact ⟨M i,c i,fun h => False.elim (hi h)⟩
  choose Q g hQg using hExists
  have hQ := fun i hqi hit => (hQg i ⟨hqi,hit⟩).1
  have hTrace := fun i hqi hit => (hQg i ⟨hqi,hit⟩).2.1
  refine ⟨Q,g,hQ,hTrace,family_exceptional_frame F M Q hM t q hqt hQ,?_⟩
  intro j
  constructor
  · cases h : familyColors c g t q j <;> simp [branchSign,h]
  · intro a
    dsimp only
    by_cases hj : j = q
    · subst j
      have ho : familyObjects M Q t q q = M t := by simp [familyObjects]
      rw [ho]
      have hd := hD t a
      rw [hc] at hd
      simpa [familyColors,branchSign,negateColumn,leftSweep_entries U D t q hqt] using hd
    · by_cases hji : q < j ∧ j ≤ t
      · have hp : q ≤ predecessor j ∧ predecessor j < t := by
          change q.val ≤ j.val-1 ∧ j.val-1 < t.val
          constructor <;> omega
        have ho : familyObjects M Q t q j = Q (predecessor j) := by simp [familyObjects,hj,hji]
        have hcol : familyColors c g t q j = g (predecessor j) := by simp [familyColors,hj,hji]
        have hpred : predecessor j = j-1 := predecessor_eq_sub_one j (by omega)
        rw [ho,hcol]
        simp only [negateColumn,if_neg hj,leftSweep_entries U D t q hqt,if_pos hji,←hpred]
        exact (hQg _ hp).2.2 a
      · have ho : familyObjects M Q t q j = M j := by simp [familyObjects,hj,hji]
        have hcol : familyColors c g t q j = c j := by simp [familyColors,hj,hji]
        rw [ho,hcol]
        simp only [negateColumn,if_neg hj,leftSweep_entries U D t q hqt,if_neg hji]
        exact hD j a

#print axioms signed_red_pivot_weight
#print axioms construct_traced_red_family
end QuiverProofs.MA4RestartArrow20261003.RedFamilyConstruction
