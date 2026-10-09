import QuiverProofs.MAExistenceTeamBRootOrderClosure

/-! Actual reflection-word deletion and four-label projective-root exhaustion.

A simple word taking a positive genuine initial orbit root negative admits an
explicit one-letter deletion after multiplication by that root reflection.
This yields descent for the actual simple-generator word length and classifies
the four positive roots taken negative by the inverse word [3, 2, 1, 0].
No Coxeter presentation, faithfulness, reflection-length premise, categorical
realization, Hom–Ext no-cycle theorem, or all-word mutation closure is assumed
or concluded. The fixed-label word has its initial topological interpretation
only when the initial labels are ordered accordingly.
-/
namespace QuiverProofs.MAExistenceTeamBRootWordExchange
open QuiverProofs QuiverProofs.MAExistenceLiterature
open QuiverProofs.MAExistenceTeamBRootPositivity
open QuiverProofs.MAExistenceTeamCRootSigns
open QuiverProofs.MAExistenceTeamBRootOrderClosure
set_option maxHeartbeats 0


def rootPerm (A : Matrix 4) (r : Vector4) (hn : pairing A r r = 2) :
    Equiv.Perm Vector4 where
  toFun := reflection A r
  invFun := reflection A r
  left_inv x := reflection_involutive A r x hn
  right_inv x := reflection_involutive A r x hn

@[simp] theorem rootPerm_apply (A : Matrix 4) (r x : Vector4)
    (hn : pairing A r r = 2) : rootPerm A r hn x = reflection A r x := rfl

theorem wordPerm_realRoot (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (w : List (Fin 4)) (x : Vector4) (hx : RealRoot A x) :
    RealRoot A (wordPerm A hd w x) := by
  induction w with
  | nil => simpa using hx
  | cons k w ih =>
      simpa only [wordPerm_cons, Equiv.Perm.mul_apply, simplePerm_apply] using
        RealRoot.reflect k ih

theorem wordPerm_reflection_covariant (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (w : List (Fin 4)) (r x : Vector4) :
    wordPerm A hd w (reflection A r x) =
      reflection A (wordPerm A hd w r) (wordPerm A hd w x) := by
  induction w with
  | nil => rfl
  | cons k w ih =>
      simp only [wordPerm_cons, Equiv.Perm.mul_apply, simplePerm_apply]
      rw [ih]
      exact (reflection_covariant A hA (simple k)
        (wordPerm A hd w r) (wordPerm A hd w x)
        (by rw [pairing_simple_self, hd])).symm

theorem word_sign_flip (B : Matrix 4) (hB : SkewSymmetric B)
    (w : List (Fin 4)) (x : Vector4)
    (hr : RealRoot (initialCompanion B) x)
    (hx : CoordinateNonnegative x)
    (hw : CoordinateNonpositive
      (wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1 w x)) :
    ∃ u : List (Fin 4), ∃ k : Fin 4, ∃ v : List (Fin 4),
      w = u ++ k :: v ∧
        wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1 v x =
          simple k := by
  let A := initialCompanion B
  let hd := (initialCompanion_quasiCartan B hB).2.1
  change CoordinateNonpositive (wordPerm A hd w x) at hw
  change ∃ u, ∃ k, ∃ v, w = u ++ k :: v ∧ wordPerm A hd v x = simple k
  induction w with
  | nil =>
      have hz : x = (fun _ => 0) := by
        funext i
        have hp := hx i
        have hn := hw i
        simp only [wordPerm_nil, Equiv.Perm.one_apply] at hn
        omega
      obtain ⟨i, hi⟩ := realRoot_nonzero A
        (initialCompanion_quasiCartan B hB).1 hd hr
      exact False.elim (hi (by rw [hz]))
  | cons k w ih =>
      have hrw := wordPerm_realRoot A hd w x hr
      rcases initial_realRoot_coordinateDichotomy B hB hrw with hp | hn
      · have hs : wordPerm A hd w x = simple k := by
          apply (positive_realRoot_reflection_nonpositive_iff B hB
            (wordPerm A hd w x) k hrw hp).mp
          simpa only [wordPerm_cons, Equiv.Perm.mul_apply, simplePerm_apply] using hw
        exact ⟨[], k, w, rfl, hs⟩
      · obtain ⟨u, j, v, he, hs⟩ := ih hn
        exact ⟨k :: u, j, v, by simp [he], hs⟩

theorem word_delete_at_simple_image (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (u v : List (Fin 4)) (k : Fin 4) (x : Vector4)
    (hn : pairing A x x = 2) (hv : wordPerm A hd v x = simple k) :
    wordPerm A hd (u ++ k :: v) * rootPerm A x hn =
      wordPerm A hd (u ++ v) := by
  apply Equiv.ext
  intro y
  simp only [wordPerm_append, wordPerm_cons, Equiv.Perm.mul_apply, rootPerm_apply]
  rw [wordPerm_reflection_covariant A hA hd v x y, hv]
  change wordPerm A hd u
    (simpleReflection A k (simpleReflection A k (wordPerm A hd v y))) = _
  rw [show simpleReflection A k (simpleReflection A k (wordPerm A hd v y)) =
    wordPerm A hd v y from
      reflection_involutive A (simple k) (wordPerm A hd v y)
        (by rw [pairing_simple_self, hd])]

/-- Actual orbit sign dichotomy yields a one-letter deletion, for any word
sending a positive genuine root to a negative root. No abstract Coxeter
presentation, faithfulness, exchange condition, or reflection-length premise
is assumed. -/
theorem positive_root_word_deletion (B : Matrix 4) (hB : SkewSymmetric B)
    (w : List (Fin 4)) (x : Vector4)
    (hr : RealRoot (initialCompanion B) x)
    (hx : CoordinateNonnegative x)
    (hw : CoordinateNonpositive
      (wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1 w x)) :
    ∃ u : List (Fin 4), ∃ k : Fin 4, ∃ v : List (Fin 4),
      w = u ++ k :: v ∧
        wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1 w *
          rootPerm (initialCompanion B) x
            (realRoot_norm_two _ (initialCompanion_quasiCartan B hB).1
              (initialCompanion_quasiCartan B hB).2.1 hr) =
          wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1 (u ++ v) := by
  obtain ⟨u, k, v, he, hs⟩ := word_sign_flip B hB w x hr hx hw
  refine ⟨u, k, v, he, ?_⟩
  rw [he]
  exact word_delete_at_simple_image _ (initialCompanion_quasiCartan B hB).1
    (initialCompanion_quasiCartan B hB).2.1 u v k x _ hs

theorem rootPerm_mem_reflectionGroup (A : Matrix 4)
    (hA : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 2)
    (x : Vector4) (hr : RealRoot A x) :
    rootPerm A x (realRoot_norm_two A hA hd hr) ∈ reflectionGroup A hd := by
  obtain ⟨w, k, hx⟩ := realRoot_word A hd hr
  refine ⟨w ++ [k] ++ w.reverse, ?_⟩
  apply Equiv.ext
  intro y
  simp only [wordPerm_append, wordPerm_cons, wordPerm_nil, mul_one,
    Equiv.Perm.mul_apply, simplePerm_apply, wordPerm_reverse, rootPerm_apply]
  change wordPerm A hd w
    (reflection A (simple k) ((wordPerm A hd w)⁻¹ y)) = reflection A x y
  rw [wordPerm_reflection_covariant A hA hd w (simple k), ← hx]
  simp

def rootElement (A : Matrix 4) (hA : ∀ i j, A i j = A j i)
    (hd : ∀ i, A i i = 2) (x : Vector4) (hr : RealRoot A x) :
    ReflectionGroup A hd :=
  ⟨rootPerm A x (realRoot_norm_two A hA hd hr),
    rootPerm_mem_reflectionGroup A hA hd x hr⟩

@[simp] theorem rootElement_val (A : Matrix 4) (hA : ∀ i j, A i j = A j i)
    (hd : ∀ i, A i i = 2) (x : Vector4) (hr : RealRoot A x) :
    (rootElement A hA hd x hr).val =
      rootPerm A x (realRoot_norm_two A hA hd hr) := rfl

/-- Genuine-root right multiplication decreases actual simple-generator
word length whenever the group element takes that positive root negative.
This follows from explicit word deletion, without a Coxeter presentation. -/
theorem wordLength_mul_root_descent (B : Matrix 4) (hB : SkewSymmetric B)
    (g : ReflectionGroup (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1)
    (x : Vector4) (hr : RealRoot (initialCompanion B) x)
    (hx : CoordinateNonnegative x) (hg : CoordinateNonpositive (g.val x)) :
    wordLength (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1
      (g * rootElement (initialCompanion B) (initialCompanion_quasiCartan B hB).1
        (initialCompanion_quasiCartan B hB).2.1 x hr) <
      wordLength (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1 g := by
  let A := initialCompanion B
  let hd := (initialCompanion_quasiCartan B hB).2.1
  change wordLength A hd
    (g * rootElement A (initialCompanion_quasiCartan B hB).1 hd x hr) < wordLength A hd g
  obtain ⟨w, hl, he⟩ := exists_minimal_word A hd g
  have hv : wordPerm A hd w = g.val := congrArg Subtype.val he
  have hw : CoordinateNonpositive (wordPerm A hd w x) := by simpa only [hv] using hg
  obtain ⟨u, k, v, hwv, hdel⟩ := positive_root_word_deletion B hB w x hr hx hw
  have heq : g * rootElement A (initialCompanion_quasiCartan B hB).1 hd x hr =
      wordElement A hd (u ++ v) := by
    apply Subtype.ext
    change g.val * rootPerm A x
      (realRoot_norm_two A (initialCompanion_quasiCartan B hB).1 hd hr) =
        wordPerm A hd (u ++ v)
    rw [←hv]
    exact hdel
  rw [heq]
  have hb := wordLength_le A hd (u ++ v)
  have hn : w.length = u.length + 1 + v.length := by
    rw [hwv, List.length_append, List.length_cons]
    omega
  simp only [List.length_append] at hb
  omega

private theorem fin4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

def prefixWord (k : Fin 4) : List (Fin 4) :=
  if k = 0 then [] else if k = 1 then [0] else if k = 2 then [0, 1] else [0, 1, 2]

def afterWord (k : Fin 4) : List (Fin 4) :=
  if k = 0 then [3, 2, 1] else if k = 1 then [3, 2] else if k = 2 then [3] else []

def projectiveRoot (B : Matrix 4) (hB : SkewSymmetric B) (k : Fin 4) : Vector4 :=
  wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1
    (prefixWord k) (simple k)

def inverseCoxeter (B : Matrix 4) (hB : SkewSymmetric B) : Equiv.Perm Vector4 :=
  wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1 [3, 2, 1, 0]

theorem wordPerm_coordinate_of_not_mem (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (w : List (Fin 4)) (x : Vector4) (i : Fin 4) (hi : i ∉ w) :
    wordPerm A hd w x i = x i := by
  induction w with
  | nil => rfl
  | cons k w ih =>
      have hik : i ≠ k := by
        intro he
        exact hi (List.mem_cons.mpr (Or.inl he))
      have hiw : i ∉ w := by
        intro he
        exact hi (List.mem_cons.mpr (Or.inr he))
      simp only [wordPerm_cons, Equiv.Perm.mul_apply, simplePerm_apply]
      rw [simpleReflection_apply_ne _ k i hik, ih hiw]

theorem projectiveRoot_realRoot (B : Matrix 4) (hB : SkewSymmetric B) (k : Fin 4) :
    RealRoot (initialCompanion B) (projectiveRoot B hB k) :=
  wordPerm_realRoot _ _ _ _ (RealRoot.simple k)

theorem projectiveRoot_coordinate_self (B : Matrix 4) (hB : SkewSymmetric B) (k : Fin 4) :
    projectiveRoot B hB k k = 1 := by
  have hk : k ∉ prefixWord k := by
    rcases fin4 k with rfl | rfl | rfl | rfl <;> decide
  rw [projectiveRoot, wordPerm_coordinate_of_not_mem _ _ _ _ k hk]
  simp [simple]

theorem projectiveRoot_nonnegative (B : Matrix 4) (hB : SkewSymmetric B) (k : Fin 4) :
    CoordinateNonnegative (projectiveRoot B hB k) := by
  rcases initial_realRoot_coordinateDichotomy B hB (projectiveRoot_realRoot B hB k) with hp | hn
  · exact hp
  · have h := hn k
    rw [projectiveRoot_coordinate_self] at h
    omega

theorem projectiveRoot_coordinate_above (B : Matrix 4) (hB : SkewSymmetric B)
    (k j : Fin 4) (hkj : k < j) : projectiveRoot B hB k j = 0 := by
  have hj : j ∉ prefixWord k := by
    rcases fin4 k with rfl | rfl | rfl | rfl <;>
      rcases fin4 j with rfl | rfl | rfl | rfl <;> first | decide | omega
  have hne : j ≠ k := by omega
  rw [projectiveRoot, wordPerm_coordinate_of_not_mem _ _ _ _ j hj]
  simp [simple, hne]

theorem projectiveRoot_injective (B : Matrix 4) (hB : SkewSymmetric B) :
    Function.Injective (projectiveRoot B hB) := by
  intro k j he
  by_contra h
  have hord : k < j ∨ j < k := by omega
  rcases hord with hkj | hjk
  · have hc := congrArg (fun x => x j) he
    change projectiveRoot B hB k j = projectiveRoot B hB j j at hc
    rw [projectiveRoot_coordinate_above B hB k j hkj, projectiveRoot_coordinate_self] at hc
    omega
  · have hc := congrArg (fun x => x k) he
    change projectiveRoot B hB k k = projectiveRoot B hB j k at hc
    rw [projectiveRoot_coordinate_self, projectiveRoot_coordinate_above B hB j k hjk] at hc
    omega

/-- Positive genuine roots sent negative by the inverse four-label Coxeter
word are exhausted by its four suffix roots. This is a finite word-position
argument, with no bounded mutation search or Coxeter presentation. -/
theorem inverseCoxeter_negative_root_exhaustion (B : Matrix 4) (hB : SkewSymmetric B)
    (x : Vector4) (hr : RealRoot (initialCompanion B) x)
    (hx : CoordinateNonnegative x) (hc : CoordinateNonpositive (inverseCoxeter B hB x)) :
    ∃ k, x = projectiveRoot B hB k := by
  obtain ⟨u, k, v, he, hs⟩ := word_sign_flip B hB [3, 2, 1, 0] x hr hx hc
  have hroot : x = wordPerm (initialCompanion B)
      (initialCompanion_quasiCartan B hB).2.1 v.reverse (simple k) := by
    rw [wordPerm_reverse, ← hs]
    simp
  cases u with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      exact ⟨3, by simpa [projectiveRoot, prefixWord] using hroot⟩
  | cons a u =>
      simp only [List.cons_append, List.cons.injEq] at he
      rcases he with ⟨rfl, he⟩
      cases u with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨2, by simpa [projectiveRoot, prefixWord] using hroot⟩
      | cons a u =>
          simp only [List.cons_append, List.cons.injEq] at he
          rcases he with ⟨rfl, he⟩
          cases u with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at he
              rcases he with ⟨rfl, rfl⟩
              exact ⟨1, by simpa [projectiveRoot, prefixWord] using hroot⟩
          | cons a u =>
              simp only [List.cons_append, List.cons.injEq] at he
              rcases he with ⟨rfl, he⟩
              cases u with
              | nil =>
                  simp only [List.nil_append, List.cons.injEq] at he
                  rcases he with ⟨rfl, rfl⟩
                  exact ⟨0, by simpa [projectiveRoot, prefixWord] using hroot⟩
              | cons a u => simp at he

private theorem simplePerm_apply_twice (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (k : Fin 4) (x : Vector4) : simplePerm A hd k (simplePerm A hd k x) = x :=
  reflection_involutive A (simple k) x (by rw [pairing_simple_self, hd])

private theorem simplePerm_simple_self (A : Matrix 4) (hd : ∀ i, A i i = 2)
    (k : Fin 4) : simplePerm A hd k (simple k) = fun i => -simple k i :=
  simpleReflection_simple_self A hd k

theorem inverseCoxeter_projectiveRoot_formula (B : Matrix 4)
    (hB : SkewSymmetric B) (k : Fin 4) :
    inverseCoxeter B hB (projectiveRoot B hB k) =
      wordPerm (initialCompanion B) (initialCompanion_quasiCartan B hB).2.1
        (afterWord k) (fun i => -simple k i) := by
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  rcases fin4 k with rfl | rfl | rfl | rfl
  all_goals
    dsimp only [inverseCoxeter, projectiveRoot, prefixWord, afterWord]
    simp only [h10, h20, h21, h30, h31, h32, ↓reduceIte,
      wordPerm_cons, wordPerm_nil, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      simplePerm_apply_twice, simplePerm_simple_self]

theorem inverseCoxeter_projectiveRoot_nonpositive (B : Matrix 4)
    (hB : SkewSymmetric B) (k : Fin 4) :
    CoordinateNonpositive (inverseCoxeter B hB (projectiveRoot B hB k)) := by
  have hk : k ∉ afterWord k := by
    rcases fin4 k with rfl | rfl | rfl | rfl <;> decide
  have hself : inverseCoxeter B hB (projectiveRoot B hB k) k = -1 := by
    rw [inverseCoxeter_projectiveRoot_formula, wordPerm_coordinate_of_not_mem _ _ _ _ k hk]
    simp [simple]
  have hr := wordPerm_realRoot (initialCompanion B)
    (initialCompanion_quasiCartan B hB).2.1 [3, 2, 1, 0]
    (projectiveRoot B hB k) (projectiveRoot_realRoot B hB k)
  rcases initial_realRoot_coordinateDichotomy B hB hr with hp | hn
  · have h := hp k
    change 0 ≤ inverseCoxeter B hB (projectiveRoot B hB k) k at h
    rw [hself] at h
    omega
  · exact hn

theorem inverseCoxeter_negative_root_iff (B : Matrix 4) (hB : SkewSymmetric B)
    (x : Vector4) (hr : RealRoot (initialCompanion B) x)
    (hx : CoordinateNonnegative x) :
    CoordinateNonpositive (inverseCoxeter B hB x) ↔ ∃ k, x = projectiveRoot B hB k := by
  constructor
  · exact inverseCoxeter_negative_root_exhaustion B hB x hr hx
  · rintro ⟨k, rfl⟩
    exact inverseCoxeter_projectiveRoot_nonpositive B hB k

end QuiverProofs.MAExistenceTeamBRootWordExchange
