import Rank4C7A41E.BoundDecision

/-! A finite integer encoding of a core with graph-theoretic fork exits.
Frames are checked by exhaustive permutation indices; no proof-bearing
framing witness or external transition labels are trusted by acceptance.
This certificate language is sound and is not asserted complete.
-/
namespace Rank4C7A41E
open QuiverProofs

structure SixEntries where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int

def SixEntries.matrix (x : SixEntries) : Matrix 4 :=
  ofSix x.a x.b x.c x.d x.e x.f

theorem SixEntries.skew (x : SixEntries) : SkewSymmetric x.matrix :=
  ofSix_skew _ _ _ _ _ _

structure GraphCoreCertificate where
  size : Nat
  root : Fin size
  node : Fin size → SixEntries
  entry : List (Fin 4)

def GraphCoreCertificate.matrices (c : GraphCoreCertificate) : Fin c.size → Matrix 4 :=
  fun i => (c.node i).matrix

local instance graphForkDecision (B : Matrix 4) (r : Fin 4) :
    Decidable (ForkDefinition.GraphFork B r) := ForkPruning.graphForkDecidable B r

def GraphCoreChecks (Q : Rank4Input) (c : GraphCoreCertificate) : Prop :=
  (∃ p : Fin 24, CertificateSearch.EntriesEqual (applyWord Q.val c.entry)
    (relabel (c.matrices c.root) (Census.permutation p))) ∧
  (∀ i, ¬ ForkPruning.FiniteAcyclic (c.matrices i)) ∧
  ∀ i k, (∃ j : Fin c.size, ∃ p : Fin 24,
    CertificateSearch.EntriesEqual (mutate (c.matrices i) k)
      (relabel (c.matrices j) (Census.permutation p))) ∨
    ForkDefinition.GraphFork (mutate (c.matrices i) k) k

instance (Q : Rank4Input) (c : GraphCoreCertificate) : Decidable (GraphCoreChecks Q c) := by
  unfold GraphCoreChecks
  infer_instance

def checkGraphCore (Q : Rank4Input) (c : GraphCoreCertificate) : Bool :=
  decide (GraphCoreChecks Q c)

theorem checkGraphCore_iff (Q : Rank4Input) (c : GraphCoreCertificate) :
    checkGraphCore Q c = true ↔ GraphCoreChecks Q c := by
  simp only [checkGraphCore, decide_eq_true_eq]

theorem checkGraphCore_sound (Q : Rank4Input) (c : GraphCoreCertificate)
    (h : checkGraphCore Q c = true) : ¬ MutationAcyclic Q.val := by
  obtain ⟨⟨p, he⟩, hc, hclosed⟩ := (checkGraphCore_iff Q c).mp h
  have cyclic : ∀ i, ¬ Acyclic (c.matrices i) := by
    intro i ha
    exact hc i ((ForkPruning.finiteAcyclic_iff _ (c.node i).skew).mpr ha)
  have closed : ∀ i k,
      Forks.FramedCore c.matrices (mutate (c.matrices i) k) ∨
        Forks.IsFork (mutate (c.matrices i) k) k := by
    intro i k
    rcases hclosed i k with ⟨j, q, hq⟩ | hf
    · exact Or.inl ⟨j, Census.permutation q, CertificateSearch.entriesEqual_eq hq⟩
    · exact Or.inr (ForkDefinition.graphFork_to_framed _ _ hf)
  have hn := Forks.framed_core_NMA c.matrices cyclic closed c.root
  intro hm
  have endpointMA := (mutationAcyclic_word_iff Q.val c.entry).mpr hm
  rw [CertificateSearch.entriesEqual_eq he] at endpointMA
  exact hn ((MA_relabel_iff _ (Census.permutation p)).mp endpointMA)

#print axioms checkGraphCore
#print axioms checkGraphCore_sound
end Rank4C7A41E
