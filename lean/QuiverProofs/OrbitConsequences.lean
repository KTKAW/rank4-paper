import QuiverProofs.FiniteLogic

namespace QuiverProofs.OrbitConsequences
open FiniteLogic

def ArbitrarilyFarNonfork (B : Matrix 4) : Prop :=
  ∀ radius : Nat, ∃ word : List (Fin 4),
    (∀ r, ¬ Forks.IsFork (applyWord B word) r) ∧
    ∀ short : List (Fin 4), short.length ≤ radius → ∀ p : Relabeling 4,
      applyWord B word ≠ relabel (applyWord B short) p

theorem abundant_relabel (B : Matrix 4) (p : Relabeling 4)
    (h : Cone.Abundant B) : Cone.Abundant (relabel B p) := by
  intro i j hij
  exact h _ _ (fun he => hij (p.injective he))

/-- A framed, reachable cone entry suffices for unbounded distance from the
original quiver. Labels may change at every step because mutations commute
with relabeling. No shortest-path computation or external graph axiom is used. -/
theorem cone_entry_far (B : Matrix 4) (entry : List (Fin 4)) (p : Relabeling 4)
    (u v w : Int) (s : Cone.State)
    (he : relabel (applyWord B entry) p = Cone.quiver u v w s)
    (hu : 1≤u) (hv : 1≤v) (hw : 1≤w)
    (hc : Cone.InCone v s.A s.H s.Z) (hg : 2≤Cone.growth u v w)
    (hunit : u=1 ∨ v=1 ∨ w=1) : ArbitrarilyFarNonfork B := by
  intro radius
  obtain ⟨n,hn⟩ := Cone.mutation_orbit_escapes_finite_relabelings
    u v w s hu hv hw hc hg (ball B radius)
  let word := entry ++ (Cone.repeatedWord n).map p.toFun
  have hwrd : relabel (applyWord B word) p =
      applyWord (Cone.quiver u v w s) (Cone.repeatedWord n) := by
    simp only [word,applyWord_append,← word_relabel,he]
  refine ⟨word,?_,?_⟩
  · intro r hf
    have ha := abundant_relabel _ p (fork_abundant hf)
    rw [hwrd] at ha
    exact Cone.mutation_orbit_not_abundant u v w s hu hv hw hc hunit n ha
  · intro short hlen q hsame
    apply hn (applyWord B short) (word_mem_ball B short radius hlen)
      (q.trans p).toFun
    rw [← hwrd,hsame]
    rfl

theorem E1_arbitrarily_far :
    ArbitrarilyFarNonfork (ofSix (-2) (-2) 1 (-1) 2 (-2)) := by
  exact cone_entry_far _ [] (.identity 4) 2 2 1 ⟨1,2,2⟩ rfl
    (by decide) (by decide) (by decide) (by unfold Cone.InCone; decide) (by decide) (by decide)

theorem E2_arbitrarily_far :
    ArbitrarilyFarNonfork (ofSix (-2) (-1) 1 (-1) 1 (-2)) := by
  exact cone_entry_far _ [0,1,2,0,1,2] (.identity 4) 2 1 1 ⟨37,5,18⟩
    Cone.E2_enters_cone (by decide) (by decide) (by decide)
    (by unfold Cone.InCone; decide) (by decide) (by decide)

def swap12 : Relabeling 4 :=
  ⟨Cone.swap12,Cone.swap12,Cone.swap12_involutive,Cone.swap12_involutive⟩

theorem E3_arbitrarily_far :
    ArbitrarilyFarNonfork (ofSix (-2) (-1) 1 1 (-2) 2) := by
  exact cone_entry_far _ [] swap12 1 2 1 ⟨1,2,2⟩ Cone.E3_relabels_into_cone
    (by decide) (by decide) (by decide) (by unfold Cone.InCone; decide) (by decide) (by decide)

theorem E4_arbitrarily_far :
    ArbitrarilyFarNonfork (ofSix (-2) (-1) 2 (-2) (-1) (-2)) := by
  exact cone_entry_far _ [0,1,2] (.identity 4) 2 1 2 ⟨10,9,6⟩
    Cone.E4_enters_cone (by decide) (by decide) (by decide)
    (by unfold Cone.InCone; decide) (by decide) (by decide)

end QuiverProofs.OrbitConsequences
