import QuiverProofs.ConePhases
import QuiverProofs.RegionCells
import QuiverProofs.OrbitConsequences

/-! The persistent two-weak-pair obstruction to the fixed diamond/decagon
language. A weak pair has weight zero or one; its endpoints are unordered.
All parameters and mutation-word lengths are unbounded. -/
namespace QuiverProofs.ExtendedWeakPairs

def Weak (B : Matrix 4) (i j : Fin 4) : Prop :=
  i ≠ j ∧ -1 ≤ B i j ∧ B i j ≤ 1

def SamePair (i j k l : Fin 4) : Prop :=
  (i=k ∧ j=l) ∨ (i=l ∧ j=k)

def AtMostOneWeakPair (B : Matrix 4) : Prop :=
  ∀ i j k l, Weak B i j → Weak B k l → SamePair i j k l

def TwoWeakPairs (B : Matrix 4) : Prop :=
  ∃ i j k l, Weak B i j ∧ Weak B k l ∧ ¬ SamePair i j k l

theorem weak_iff_weight (B : Matrix 4) (i j : Fin 4) :
    Weak B i j ↔ i≠j ∧ (B i j).natAbs < 2 := by
  simp only [Weak]
  omega

theorem two_excludes_one {B : Matrix 4} (h : TwoWeakPairs B) :
    ¬ AtMostOneWeakPair B := by
  obtain ⟨i,j,k,l,hij,hkl,hd⟩ := h
  exact fun hu => hd (hu i j k l hij hkl)

theorem one_relabel (B : Matrix 4) (p : Relabeling 4)
    (h : AtMostOneWeakPair B) : AtMostOneWeakPair (relabel B p) := by
  intro i j k l hij hkl
  have h1 : Weak B (p.toFun i) (p.toFun j) :=
    ⟨fun he => hij.1 (p.injective he),hij.2⟩
  have h2 : Weak B (p.toFun k) (p.toFun l) :=
    ⟨fun he => hkl.1 (p.injective he),hkl.2⟩
  rcases h _ _ _ _ h1 h2 with ⟨hi,hj⟩ | ⟨hi,hj⟩
  · exact Or.inl ⟨p.injective hi,p.injective hj⟩
  · exact Or.inr ⟨p.injective hi,p.injective hj⟩

theorem one_reverse (B : Matrix 4) (h : AtMostOneWeakPair B) :
    AtMostOneWeakPair (reverse B) := by
  intro i j k l hij hkl
  apply h i j k l
  · refine ⟨hij.1,?_⟩
    have hh : -1 ≤ -B i j ∧ -B i j ≤ 1 := hij.2
    omega
  · refine ⟨hkl.1,?_⟩
    have hh : -1 ≤ -B k l ∧ -B k l ≤ 1 := hkl.2
    omega

theorem two_relabel (B : Matrix 4) (p : Relabeling 4) (h : TwoWeakPairs B) :
    TwoWeakPairs (relabel B p) := by
  obtain ⟨i,j,k,l,hij,hkl,hd⟩ := h
  refine ⟨p.invFun i,p.invFun j,p.invFun k,p.invFun l,?_,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro he; have := congrArg p.toFun he; exact hij.1 (by simpa only [p.right_inv] using this)
    · simpa only [relabel,p.right_inv] using hij.2
  · refine ⟨?_,?_⟩
    · intro he; have := congrArg p.toFun he; exact hkl.1 (by simpa only [p.right_inv] using this)
    · simpa only [relabel,p.right_inv] using hkl.2
  · intro hs
    apply hd
    rcases hs with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · exact Or.inl ⟨by have := congrArg p.toFun hi; simpa only [p.right_inv] using this,
        by have := congrArg p.toFun hj; simpa only [p.right_inv] using this⟩
    · exact Or.inr ⟨by have := congrArg p.toFun hi; simpa only [p.right_inv] using this,
        by have := congrArg p.toFun hj; simpa only [p.right_inv] using this⟩

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

/-- Five abundant coordinates leave only the sixth unordered pair weak. -/
theorem ofSix_one (a b c d e f : Int)
    (ha : 2≤a ∨ a≤ -2) (hb : 2≤b ∨ b≤ -2) (hc : 2≤c ∨ c≤ -2)
    (hd : 2≤d ∨ d≤ -2) (he : 2≤e ∨ e≤ -2) :
    AtMostOneWeakPair (ofSix a b c d e f) := by
  have special : ∀ i j, Weak (ofSix a b c d e f) i j → SamePair i j 2 3 := by
    intro i j hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;>
      rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [Weak,SamePair,ofSix] at * <;> omega
  intro i j k l hij hkl
  have hs1 := special i j hij
  have hs2 := special k l hkl
  rcases hs1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hs2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [SamePair]

theorem fork_one {B : Matrix 4} {r : Fin 4} (h : Forks.IsFork B r) :
    AtMostOneWeakPair B := by
  intro i j k l hij _
  have hb := FiniteLogic.fork_abundant h i j hij.1
  have hw := (weak_iff_weight B i j).mp hij
  omega

theorem diamond_one (A B C D E : Int) (h : Regions.Domain A B C D E)
    (i : Fin 4) : AtMostOneWeakPair (RegionCells.diamondState A B C D E i) := by
  have hp := Regions.parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  rcases fin4 i with rfl|rfl|rfl|rfl <;>
    apply ofSix_one <;> first | left; omega | right; omega

theorem unit_one (A B C D E : Int) (h : Regions.Domain A B C D E)
    (i : Fin 10) : AtMostOneWeakPair (RegionCells.unitState A B C D E i) := by
  have hp := Regions.parameter_bounds A B C D E h
  obtain ⟨hA,hD,hE,hAB,hDB,hAC,hEC⟩ := h
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals dsimp only [RegionCells.unitState]
  all_goals try apply one_relabel
  all_goals apply ofSix_one <;> first | left; omega | right; omega

/-- The fixed normalized exterior language, saturated under all label
transports and arrow reversal. Recursive nesting cannot add new state shapes. -/
inductive Exterior : Matrix 4 → Prop
  | fork {B : Matrix 4} (r : Fin 4) : Forks.IsFork B r → Exterior B
  | diamond (A B C D E : Int) : Regions.Domain A B C D E → (i : Fin 4) →
      Exterior (RegionCells.diamondState A B C D E i)
  | unit (A B C D E : Int) : Regions.Domain A B C D E → (i : Fin 10) →
      Exterior (RegionCells.unitState A B C D E i)
  | framed {B : Matrix 4} : Exterior B → (p : Relabeling 4) → Exterior (relabel B p)
  | reversed {B : Matrix 4} : Exterior B → Exterior (reverse B)

theorem exterior_one {B : Matrix 4} (h : Exterior B) : AtMostOneWeakPair B := by
  induction h with
  | fork _ hf => exact fork_one hf
  | diamond A B C D E hd i => exact diamond_one A B C D E hd i
  | unit A B C D E hd i => exact unit_one A B C D E hd i
  | framed _ p ih => exact one_relabel _ p ih
  | reversed _ ih => exact one_reverse _ ih

theorem two_not_exterior {B : Matrix 4} (h : TwoWeakPairs B) : ¬ Exterior B :=
  fun he => two_excludes_one h (exterior_one he)

theorem cone_phase_two (u v w : Int) (s : Cone.State)
    (htwo : (u=1 ∧ v=1) ∨ (u=1 ∧ w=1) ∨ (v=1 ∧ w=1)) (phase : Fin 3) :
    TwoWeakPairs (ConePhases.phaseMatrix u v w s phase) := by
  have hp : phase=0 ∨ phase=1 ∨ phase=2 := by omega
  rcases htwo with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases hp with rfl|rfl|rfl <;>
      exact ⟨0,1,0,2,by simp [Weak,ConePhases.phaseMatrix,Cone.quiver,ofSix],
        by simp [Weak,ConePhases.phaseMatrix,Cone.quiver,ofSix],by simp [SamePair]⟩
  · rcases hp with rfl|rfl|rfl <;>
      exact ⟨0,1,1,2,by simp [Weak,ConePhases.phaseMatrix,Cone.quiver,ofSix],
        by simp [Weak,ConePhases.phaseMatrix,Cone.quiver,ofSix],by simp [SamePair]⟩
  · rcases hp with rfl|rfl|rfl <;>
      exact ⟨0,2,1,2,by simp [Weak,ConePhases.phaseMatrix,Cone.quiver,ofSix],
        by simp [Weak,ConePhases.phaseMatrix,Cone.quiver,ofSix],by simp [SamePair]⟩

theorem mutation_cone_phase_two (u v w : Int) (s : Cone.State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) (hc : Cone.InCone v s.A s.H s.Z)
    (htwo : (u=1 ∧ v=1) ∨ (u=1 ∧ w=1) ∨ (v=1 ∧ w=1))
    (n : Nat) (phase : Fin 3) :
    TwoWeakPairs (applyWord (Cone.quiver u v w s) (ConePhases.phaseWord n phase)) := by
  rw [ConePhases.phase_as_mutations u v w s hu hv hw hc n phase]
  exact cone_phase_two u v w _ htwo phase

theorem cone_escapes_finite_core_and_exterior (u v w : Int) (s : Cone.State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) (hc : Cone.InCone v s.A s.H s.Z)
    (hg : 2≤Cone.growth u v w)
    (htwo : (u=1 ∧ v=1) ∨ (u=1 ∧ w=1) ∨ (v=1 ∧ w=1))
    (candidates : List (Matrix 4)) :
    ∃ n, (∀ B ∈ candidates, ∀ p : Relabeling 4,
      applyWord (Cone.quiver u v w s) (Cone.repeatedWord n) ≠ relabel B p) ∧
      ¬ Exterior (applyWord (Cone.quiver u v w s) (Cone.repeatedWord n)) := by
  obtain ⟨n,hn⟩ := Cone.mutation_orbit_escapes_finite_relabelings u v w s hu hv hw hc hg candidates
  refine ⟨n,fun B hB p => hn B hB p.toFun,?_⟩
  apply two_not_exterior
  rw [Cone.orbit_as_mutations u v w s hu hv hw hc n]
  exact cone_phase_two u v w _ htwo 0

/-- Reachability transports the finite-core obstruction to the original
printed labels. Arrow reversal in a finite core can be included simply by
listing the reversed representatives among `candidates`. -/
theorem cone_entry_escapes (B : Matrix 4) (entry : List (Fin 4)) (p : Relabeling 4)
    (u v w : Int) (s : Cone.State)
    (he : relabel (applyWord B entry) p = Cone.quiver u v w s)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) (hc : Cone.InCone v s.A s.H s.Z)
    (hg : 2≤Cone.growth u v w)
    (htwo : (u=1 ∧ v=1) ∨ (u=1 ∧ w=1) ∨ (v=1 ∧ w=1))
    (candidates : List (Matrix 4)) :
    ∃ word : List (Fin 4), TwoWeakPairs (applyWord B word) ∧
      (∀ C ∈ candidates, ∀ q : Relabeling 4, applyWord B word ≠ relabel C q) ∧
      ¬ Exterior (applyWord B word) := by
  obtain ⟨n,hn⟩ := Cone.mutation_orbit_escapes_finite_relabelings u v w s hu hv hw hc hg candidates
  let word := entry ++ (Cone.repeatedWord n).map p.toFun
  have hwrd : relabel (applyWord B word) p =
      applyWord (Cone.quiver u v w s) (Cone.repeatedWord n) := by
    simp only [word,applyWord_append,← word_relabel,he]
  have ht : TwoWeakPairs (applyWord B word) := by
    have hcone : TwoWeakPairs (applyWord (Cone.quiver u v w s) (Cone.repeatedWord n)) := by
      rw [Cone.orbit_as_mutations u v w s hu hv hw hc n]
      exact cone_phase_two u v w _ htwo 0
    rw [← hwrd] at hcone
    simpa only [relabel_inverse] using two_relabel _ p.symm hcone
  refine ⟨word,ht,?_,two_not_exterior ht⟩
  intro C hC q heq
  apply hn C hC (q.trans p).toFun
  rw [← hwrd,heq]
  rfl

def FiniteCoreExteriorCover (B : Matrix 4) : Prop :=
  ∃ candidates : List (Matrix 4), ∀ word : List (Fin 4),
    (∃ C ∈ candidates, ∃ p : Relabeling 4, applyWord B word = relabel C p) ∨
      Exterior (applyWord B word)

theorem E2_no_finite_core_exterior_cover :
    ¬ FiniteCoreExteriorCover (ofSix (-2) (-1) 1 (-1) 1 (-2)) := by
  rintro ⟨candidates,hcover⟩
  obtain ⟨word,_,hfinite,hext⟩ := cone_entry_escapes _ [0,1,2,0,1,2]
    (.identity 4) 2 1 1 ⟨37,5,18⟩ Cone.E2_enters_cone
    (by decide) (by decide) (by decide) (by unfold Cone.InCone; decide)
    (by decide) (by simp) candidates
  rcases hcover word with ⟨C,hC,p,hp⟩ | hs
  · exact hfinite C hC p hp
  · exact hext hs

theorem E3_no_finite_core_exterior_cover :
    ¬ FiniteCoreExteriorCover (ofSix (-2) (-1) 1 1 (-2) 2) := by
  rintro ⟨candidates,hcover⟩
  obtain ⟨word,_,hfinite,hext⟩ := cone_entry_escapes (ofSix (-2) (-1) 1 1 (-2) 2) [] OrbitConsequences.swap12
    1 2 1 ⟨1,2,2⟩ Cone.E3_relabels_into_cone
    (by decide) (by decide) (by decide) (by unfold Cone.InCone; decide)
    (by decide) (by simp) candidates
  rcases hcover word with ⟨C,hC,p,hp⟩ | hs
  · exact hfinite C hC p hp
  · exact hext hs

end QuiverProofs.ExtendedWeakPairs
