import QuiverProofs.ProperWiggleInvariants

/-! Proper mutations and total properness as genuine unbounded reachability
properties. This module does not assume that mutation-acyclic quivers are
totally proper, nor that an arbitrary proper class is totally proper. -/
namespace QuiverProofs.ProperMutation
open ProperOrder ProperWiggle

def cutOrder (c : Fin 4) : CyclicOrder :=
  Census.permutation (match c.val with | 0 => 0 | 1 => 6 | 2 => 8 | _ => 9)

/-- After tearing at the mutation vertex, outgoing neighbors precede incoming
neighbors. Nonneighbors may be assigned to either side of the cut. -/
def Cut (B : Matrix 4) (r : CyclicOrder) (c : Fin 4) : Prop :=
  let a := B (r.toFun 0) (r.toFun 1)
  let b := B (r.toFun 0) (r.toFun 2)
  let d := B (r.toFun 0) (r.toFun 3)
  match c.val with
  | 0 => a ≤ 0 ∧ b ≤ 0 ∧ d ≤ 0
  | 1 => 0 ≤ a ∧ b ≤ 0 ∧ d ≤ 0
  | 2 => 0 ≤ a ∧ 0 ≤ b ∧ d ≤ 0
  | _ => 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ d

/-- Move the mutation vertex past its outgoing block, preserving the relative
order of the other vertices. Both endpoints denote whole wiggle classes. -/
def ProperMutation (B : Matrix 4) (p : CyclicOrder) (k : Fin 4)
    (q : CyclicOrder) : Prop :=
  ∃ r : CyclicOrder, ∃ c : Fin 4,
    WiggleEquivalent B p r ∧ r.toFun 0 = k ∧ Cut B r c ∧
    WiggleEquivalent (mutate B k) (r.trans (cutOrder c)) q

private theorem proper_in_frame (B : Matrix 4) (r : CyclicOrder)
    (h : ProperVertex B r (r.toFun 0)) :
    ProperVertex (relabel B r) (Census.permutation 0) 0 := by
  intro u w huv hvw
  have hh := h (r.toFun u) (r.toFun w) huv hvw
  have hid : (Census.permutation 0).invFun = id := by
    funext i
    exact (show ∀ i : Fin 4, (Census.permutation 0).invFun i = i by decide) i
  simpa only [Between,hid,r.left_inv] using hh

/-- A proper vertex always admits the outgoing/incoming cut used in the rule. -/
theorem proper_vertex_has_cut (B : Matrix 4) (hB : SkewSymmetric B)
    (r : CyclicOrder) (h : ProperVertex B r (r.toFun 0)) :
    ∃ c : Fin 4, Cut B r c := by
  have hframe := proper_in_frame B r h
  have hrec := ofSix_reconstruct (relabel B r) (relabel_skew B r hB)
  rw [← hrec] at hframe
  rcases proper_zero_has_cut _ _ _ _ _ _ hframe with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩

/-- Properness of a class supplies a proper mutation at each requested vertex;
the representative used may depend on that vertex. -/
theorem properClass_has_mutation (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) (h : ProperClass B p) (k : Fin 4) :
    ∃ q : CyclicOrder, ProperMutation B p k q := by
  obtain ⟨r,hr,hv⟩ := h k
  obtain ⟨s,hrs,hsk⟩ := ProperWiggleInvariants.exists_first_representative r k
  have hs : ProperVertex B s (s.toFun 0) := by
    rw [hsk]
    exact (properVertex_cyclic B r s hrs k).mp hv
  obtain ⟨c,hc⟩ := proper_vertex_has_cut B hB s hs
  refine ⟨s.trans (cutOrder c),s,c,.trans hr (.same hrs),hsk,hc,?_⟩
  exact .same (fun _ _ _ => Iff.rfl)

/-- The local proper-mutation rule preserves the order-dependent coefficient
in every labeling, with the chosen order transported. -/
theorem cut_markov (B : Matrix 4) (hB : SkewSymmetric B)
    (r : CyclicOrder) (c : Fin 4) (hc : Cut B r c) :
    orderMarkov (mutate B (r.toFun 0)) (r.trans (cutOrder c)) = orderMarkov B r := by
  have hrec := ofSix_reconstruct (relabel B r) (relabel_skew B r hB)
  have ht : orderMarkov (mutate (relabel B r) 0) (cutOrder c) =
      orderMarkov (relabel B r) (Census.permutation 0) := by
    rw [← hrec]
    have hcases : c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact markov_proper_cut_zero _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2
    · exact markov_proper_cut_one _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2
    · exact markov_proper_cut_two _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2
    · exact markov_proper_cut_three _ _ _ _ _ _ hc.1 hc.2.1 hc.2.2
  rw [mutate_relabel] at ht
  exact ht

/-- Scalar transport on whole wiggle classes, independent of zero-edge choices. -/
theorem properMutation_markov (B : Matrix 4) (hB : SkewSymmetric B)
    {p q : CyclicOrder} {k : Fin 4} (h : ProperMutation B p k q) :
    orderMarkov (mutate B k) q = orderMarkov B p := by
  obtain ⟨r,c,hpr,hk,hc,hrq⟩ := h
  have h1 := ProperWiggleInvariants.markov_wiggle_invariant B hB hpr
  have h2 := ProperWiggleInvariants.markov_wiggle_invariant (mutate B k)
    (mutation_preserves_skew B k hB) hrq
  rw [← hk] at h2 ⊢
  exact h2.symm.trans ((cut_markov B hB r c hc).trans h1.symm)

/-- Finite proper transport, with no depth cutoff. -/
inductive Transport (B : Matrix 4) (p : CyclicOrder) : Matrix 4 → CyclicOrder → Prop
  | refl : Transport B p B p
  | step {C : Matrix 4} {q r : CyclicOrder} {k : Fin 4} :
      Transport B p C q → ProperMutation C q k r → Transport B p (mutate C k) r

/-- Every finite proper-mutation descendant is a proper class. -/
def TotalProper (B : Matrix 4) (p : CyclicOrder) : Prop :=
  ∀ C q, Transport B p C q → ProperClass C q

theorem totalProper_proper (B : Matrix 4) (p : CyclicOrder)
    (h : TotalProper B p) : ProperClass B p := h B p .refl

theorem transport_trans {B C D : Matrix 4} {p q r : CyclicOrder}
    (h : Transport B p C q) (g : Transport C q D r) : Transport B p D r := by
  induction g with
  | refl => exact h
  | step _ hg ih => exact .step ih hg

theorem totalProper_transport {B C : Matrix 4} {p q : CyclicOrder}
    (h : TotalProper B p) (g : Transport B p C q) : TotalProper C q := by
  intro D r hd
  exact h D r (transport_trans g hd)

theorem transport_reachable {B C : Matrix 4} {p q : CyclicOrder}
    (h : Transport B p C q) : ∃ w : List (Fin 4), C = applyWord B w := by
  induction h with
  | refl => exact ⟨[],rfl⟩
  | @step C q r k _ _ ih =>
    obtain ⟨w,hw⟩ := ih
    exact ⟨w ++ [k],by rw [applyWord_append]; simpa only [applyWord] using congrArg (fun M => mutate M k) hw⟩

theorem transport_skew {B C : Matrix 4} {p q : CyclicOrder}
    (hB : SkewSymmetric B) (h : Transport B p C q) : SkewSymmetric C := by
  obtain ⟨w,hw⟩ := transport_reachable h
  rw [hw]
  exact word_preserves_skew B w hB

/-- Every finite sequence of proper mutations preserves the transported
Markov coefficient. This theorem has no mutation-depth or weight bound. -/
theorem transport_markov {B C : Matrix 4} {p q : CyclicOrder}
    (hB : SkewSymmetric B) (h : Transport B p C q) :
    orderMarkov C q = orderMarkov B p := by
  induction h with
  | refl => rfl
  | step ht hm ih =>
    exact (properMutation_markov _ (transport_skew hB ht) hm).trans ih

/-- Total properness permits lifting every ordinary finite mutation word.
It is never inferred merely from the initial class being proper. -/
theorem totalProper_lifts_word (B : Matrix 4) (hB : SkewSymmetric B)
    (p : CyclicOrder) (h : TotalProper B p) (w : List (Fin 4)) :
    ∃ q : CyclicOrder, Transport B p (applyWord B w) q ∧
      TotalProper (applyWord B w) q := by
  induction w generalizing B p with
  | nil => exact ⟨p,.refl,h⟩
  | cons k ks ih =>
    obtain ⟨r,hr⟩ := properClass_has_mutation B hB p (totalProper_proper B p h) k
    have ht : Transport B p (mutate B k) r := .step .refl hr
    have htp := totalProper_transport h ht
    obtain ⟨q,hq,htq⟩ := ih (mutate B k) (mutation_preserves_skew B k hB) r htp
    exact ⟨q,transport_trans ht hq,htq⟩

end QuiverProofs.ProperMutation
