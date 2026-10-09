import QuiverProofs.Cone
import QuiverProofs.Forks

namespace QuiverProofs.FiniteLogic

/-- Finitely many candidates cannot indefinitely evade finite separating tests.
The test type can in particular be the integer polynomials. -/
theorem finite_tests_common_target {Candidate Test : Type}
    (candidates : List Candidate) (satisfies : Candidate → Test → Prop) :
    (∀ tests : List Test, ∃ c ∈ candidates, ∀ t ∈ tests, satisfies c t) ↔
      (∃ c ∈ candidates, ∀ t, satisfies c t) := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have separating : ∀ cs : List Candidate,
        (∀ c ∈ cs, ¬ ∀ t, satisfies c t) →
        ∃ tests : List Test, ∀ c ∈ cs, ∃ t ∈ tests, ¬ satisfies c t := by
      intro cs
      induction cs with
      | nil => intro _; exact ⟨[], by simp⟩
      | cons c cs ih =>
        intro hc
        have hnot := hc c (by simp)
        have hex : ∃ t, ¬ satisfies c t := by
          apply Classical.byContradiction
          intro hh
          exact hnot (fun t => Classical.byContradiction (fun ht => hh ⟨t,ht⟩))
        obtain ⟨t,ht⟩ := hex
        obtain ⟨ts,hs⟩ := ih (fun x hx => hc x (by simp [hx]))
        refine ⟨t::ts, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨t,by simp,ht⟩
        · obtain ⟨u,hu,hm⟩ := hs x hx
          exact ⟨u,by simp [hu],hm⟩
    obtain ⟨tests,ht⟩ := separating candidates (by grind)
    obtain ⟨c,hc,hm⟩ := h tests
    obtain ⟨t,hit,hnm⟩ := ht c hc
    exact hnm (hm t hit)
  · rintro ⟨c,hc,hm⟩ tests
    exact ⟨c,hc,fun t _ => hm t⟩

/-- Every mutation word of length at most r occurs in this finite list. -/
def wordsUpTo : Nat → List (List (Fin 4))
  | 0 => [[]]
  | r+1 => [] :: ([0,1,2,3] : List (Fin 4)).flatMap
      (fun k => (wordsUpTo r).map (fun word => k::word))

theorem word_mem_wordsUpTo (word : List (Fin 4)) (r : Nat)
    (h : word.length ≤ r) : word ∈ wordsUpTo r := by
  induction r generalizing word with
  | zero =>
    have : word=[] := List.length_eq_zero_iff.mp (by omega)
    simp [this,wordsUpTo]
  | succ r ih =>
    cases word with
    | nil => simp [wordsUpTo]
    | cons k word =>
      have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
      have hm := ih word (by simpa using h)
      simp only [wordsUpTo,List.mem_cons,List.mem_flatMap,List.mem_map]
      right
      exact ⟨k,by rcases hk with rfl|rfl|rfl|rfl <;> simp,
        word,hm,rfl⟩

def ball (B : Matrix 4) (r : Nat) : List (Matrix 4) :=
  (wordsUpTo r).map (applyWord B)

theorem word_mem_ball (B : Matrix 4) (word : List (Fin 4)) (r : Nat)
    (h : word.length ≤ r) : applyWord B word ∈ ball B r :=
  List.mem_map.mpr ⟨word,word_mem_wordsUpTo word r h,rfl⟩

/-- Arbitrarily distant nonabundant descendants: no word of the given bounded
length reaches even an isomorphic representative of the exhibited descendant. -/
theorem cone_unbounded_mutation_distance (u v w : Int) (s : Cone.State)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w)
    (hc : Cone.InCone v s.A s.H s.Z) (hg : 2≤Cone.growth u v w)
    (hunit : u=1 ∨ v=1 ∨ w=1) (r : Nat) :
    ∃ n : Nat,
      ¬ Cone.Abundant (applyWord (Cone.quiver u v w s) (Cone.repeatedWord n)) ∧
      ∀ word : List (Fin 4), word.length ≤ r → ∀ p : Relabeling 4,
        applyWord (Cone.quiver u v w s) (Cone.repeatedWord n) ≠
          relabel (applyWord (Cone.quiver u v w s) word) p := by
  obtain ⟨n,hn⟩ := Cone.mutation_orbit_escapes_finite_relabelings
    u v w s hu hv hw hc hg (ball (Cone.quiver u v w s) r)
  refine ⟨n,Cone.mutation_orbit_not_abundant u v w s hu hv hw hc hunit n,?_⟩
  intro word hwlen p
  exact hn _ (word_mem_ball _ word r hwlen) p.toFun

theorem fork_abundant {B : Matrix 4} {r : Fin 4} (h : Forks.IsFork B r) :
    Cone.Abundant B := by
  induction h with
  | basic a b c d e f h =>
    obtain ⟨ha,hb,hc,had,hbd,hae,hce,hf⟩ := h
    intro i j hij
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;>
      simp [Forks.template,ofSix] at * <;> omega
  | relabelled _ p ih =>
    intro i j hij
    apply ih (p.toFun i) (p.toFun j)
    intro he
    have := congrArg p.invFun he
    simp only [p.left_inv] at this
    exact hij this
  | reversed _ ih =>
    intro i j hij
    simpa [reverse] using ih i j hij

theorem nonabundant_not_fork {B : Matrix 4} (h : ¬ Cone.Abundant B)
    (r : Fin 4) : ¬ Forks.IsFork B r := fun hf => h (fork_abundant hf)

end QuiverProofs.FiniteLogic
