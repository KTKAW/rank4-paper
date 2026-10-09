import QuiverProofs.Mutation

/- A complete labeled orbit, checked in Lean without a classification theorem. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QuiverProofs.FiniteOrbit

def state (s : Fin 24) : Matrix 4 := match s.val with
  | 0 => (ofSix (-2) (1) (1) (-1) (-1) (-1))
  | 1 => (ofSix (2) (-1) (-1) (1) (1) (-1))
  | 2 => (ofSix (-1) (-1) (1) (1) (-2) (1))
  | 3 => (ofSix (-1) (2) (-1) (-1) (1) (1))
  | 4 => (ofSix (1) (1) (-2) (-1) (1) (1))
  | 5 => (ofSix (1) (-1) (1) (2) (-1) (1))
  | 6 => (ofSix (1) (1) (-1) (1) (-1) (2))
  | 7 => (ofSix (1) (-1) (-1) (-1) (2) (-1))
  | 8 => (ofSix (1) (-2) (1) (1) (1) (-1))
  | 9 => (ofSix (-1) (-1) (2) (-1) (-1) (-1))
  | 10 => (ofSix (-1) (1) (-1) (1) (-1) (2))
  | 11 => (ofSix (-1) (1) (1) (-2) (1) (-1))
  | 12 => (ofSix (1) (-1) (1) (-1) (1) (-2))
  | 13 => (ofSix (1) (1) (-2) (1) (1) (1))
  | 14 => (ofSix (1) (-1) (-1) (2) (-1) (1))
  | 15 => (ofSix (-1) (1) (1) (1) (-2) (1))
  | 16 => (ofSix (-1) (-1) (1) (-1) (1) (-2))
  | 17 => (ofSix (-1) (2) (-1) (-1) (-1) (1))
  | 18 => (ofSix (-1) (1) (-1) (-2) (1) (-1))
  | 19 => (ofSix (-1) (-1) (2) (1) (-1) (-1))
  | 20 => (ofSix (1) (1) (-1) (-1) (2) (-1))
  | 21 => (ofSix (1) (-2) (1) (1) (-1) (-1))
  | 22 => (ofSix (-2) (1) (1) (-1) (-1) (1))
  | _ => (ofSix (2) (-1) (-1) (1) (1) (1))

def next (s : Fin 24) (k : Fin 4) : Fin 24 := match s.val, k.val with
  | 0, 0 => 1
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 4
  | 1, 3 => 5
  | 2, 0 => 6
  | 2, 1 => 7
  | 2, 2 => 0
  | 2, 3 => 7
  | 3, 0 => 8
  | 3, 1 => 6
  | 3, 2 => 8
  | 3, 3 => 0
  | 4, 0 => 9
  | 4, 1 => 10
  | 4, 2 => 1
  | 4, 3 => 9
  | 5, 0 => 10
  | 5, 1 => 11
  | 5, 2 => 11
  | 5, 3 => 1
  | 6, 0 => 2
  | 6, 1 => 3
  | 6, 2 => 12
  | 6, 3 => 12
  | 7, 0 => 11
  | 7, 1 => 2
  | 7, 2 => 13
  | 7, 3 => 2
  | 8, 0 => 3
  | 8, 1 => 9
  | 8, 2 => 3
  | 8, 3 => 14
  | 9, 0 => 4
  | 9, 1 => 8
  | 9, 2 => 15
  | 9, 3 => 4
  | 10, 0 => 5
  | 10, 1 => 4
  | 10, 2 => 16
  | 10, 3 => 16
  | 11, 0 => 7
  | 11, 1 => 5
  | 11, 2 => 5
  | 11, 3 => 17
  | 12, 0 => 18
  | 12, 1 => 19
  | 12, 2 => 6
  | 12, 3 => 6
  | 13, 0 => 19
  | 13, 1 => 17
  | 13, 2 => 7
  | 13, 3 => 19
  | 14, 0 => 15
  | 14, 1 => 18
  | 14, 2 => 18
  | 14, 3 => 8
  | 15, 0 => 14
  | 15, 1 => 20
  | 15, 2 => 9
  | 15, 3 => 20
  | 16, 0 => 20
  | 16, 1 => 21
  | 16, 2 => 10
  | 16, 3 => 10
  | 17, 0 => 21
  | 17, 1 => 13
  | 17, 2 => 21
  | 17, 3 => 11
  | 18, 0 => 12
  | 18, 1 => 14
  | 18, 2 => 14
  | 18, 3 => 22
  | 19, 0 => 13
  | 19, 1 => 12
  | 19, 2 => 22
  | 19, 3 => 13
  | 20, 0 => 16
  | 20, 1 => 15
  | 20, 2 => 23
  | 20, 3 => 15
  | 21, 0 => 17
  | 21, 1 => 16
  | 21, 2 => 17
  | 21, 3 => 23
  | 22, 0 => 23
  | 22, 1 => 23
  | 22, 2 => 19
  | 22, 3 => 18
  | 23, 0 => 22
  | 23, 1 => 22
  | 23, 2 => 20
  | 23, 3 => 21
  | _, _ => 0

theorem transition_table : ∀ (s : Fin 24) (k i j : Fin 4),
    mutate (state s) k i j = state (next s k) i j := by decide

def triangle (s : Fin 24) : Fin 4 × Fin 4 × Fin 4 := match s.val with
  | 0 => (0, 2, 1)
  | 1 => (0, 1, 2)
  | 2 => (0, 3, 1)
  | 3 => (0, 2, 1)
  | 4 => (0, 1, 3)
  | 5 => (0, 1, 2)
  | 6 => (0, 2, 3)
  | 7 => (0, 1, 3)
  | 8 => (0, 1, 2)
  | 9 => (0, 3, 1)
  | 10 => (0, 2, 3)
  | 11 => (0, 2, 1)
  | 12 => (0, 3, 2)
  | 13 => (0, 1, 3)
  | 14 => (0, 1, 2)
  | 15 => (0, 3, 1)
  | 16 => (0, 3, 2)
  | 17 => (0, 2, 1)
  | 18 => (0, 2, 1)
  | 19 => (0, 3, 1)
  | 20 => (0, 1, 3)
  | 21 => (0, 1, 2)
  | 22 => (0, 2, 1)
  | _ => (0, 1, 2)

theorem triangle_table : ∀ s : Fin 24,
    0 < state s (triangle s).1 (triangle s).2.1 ∧
    0 < state s (triangle s).2.1 (triangle s).2.2 ∧
    0 < state s (triangle s).2.2 (triangle s).1 := by decide

theorem state_not_acyclic (s : Fin 24) : ¬ Acyclic (state s) := by
  rintro ⟨rank, hr⟩
  obtain ⟨h₁, h₂, h₃⟩ := triangle_table s
  have h₁ := hr _ _ h₁
  have h₂ := hr _ _ h₂
  have h₃ := hr _ _ h₃
  omega

theorem orbit_closed (s : Fin 24) (word : List (Fin 4)) :
    ∃ t : Fin 24, applyWord (state s) word = state t := by
  induction word generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons k ks ih =>
    have h : mutate (state s) k = state (next s k) := by
      funext i j; exact transition_table s k i j
    simpa only [applyWord, h] using ih (next s k)

/-- A genuine NMA theorem: every finite mutation word remains cyclic. -/
theorem nma_q617 : ¬ MutationAcyclic (ofSix (-2) (1) (1) (-1) (-1) (-1)) := by
  rintro ⟨word, hw⟩
  obtain ⟨t, ht⟩ := orbit_closed 0 word
  exact state_not_acyclic t (ht ▸ hw)

end QuiverProofs.FiniteOrbit
