import QuiverProofs.LStarSyntax
import QuiverProofs.MatrixCache
import QuiverProofs.ForkPruningDecidable
import QuiverProofs.Regions

/-! Raw L0 boundary checks. Records contain only the exchanged matrix, return,
and special labels supplied by the Python certificate; no normal-form witness
is added. The initial prefork clauses imply the proved region normal forms. -/
namespace QuiverProofs.LStar
open ForkDefinition ForkPruning Census
open MatrixCache
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

/-- `check_fork` on an arbitrary supplied induced vertex set. -/
def ForkOnChecks (B : Matrix 4) (r : Fin 4) (vertices : Fin 4 → Prop) : Prop :=
  SkewSymmetric B ∧ vertices r ∧ ¬AcyclicOn B vertices ∧
  (∀ i j, vertices i → vertices j → i≠j → 2≤(B i j).natAbs) ∧
  AcyclicOn B (fun i => vertices i ∧ 0<B i r) ∧
  AcyclicOn B (fun i => vertices i ∧ 0<B r i) ∧
  ∀ i j, vertices i → vertices j → 0<B i r → 0<B r j →
    B i r < B j i ∧ B r j < B j i

private def forkOnChecksDecidable (B : Matrix 4) (r : Fin 4) (vertices : Fin 4 → Prop) [DecidablePred vertices] :
    Decidable (ForkOnChecks B r vertices) := by
  haveI : Decidable (SkewSymmetric B) := inferInstanceAs (Decidable (∀ i j, B i j = -B j i))
  by_cases hs : SkewSymmetric B
  · letI : Decidable (AcyclicOn B vertices) := acyclicOnDecidable B hs vertices
    letI : Decidable (AcyclicOn B (fun i => vertices i ∧ 0<B i r)) :=
      acyclicOnDecidable B hs (fun i => vertices i ∧ 0<B i r)
    letI : Decidable (AcyclicOn B (fun i => vertices i ∧ 0<B r i)) :=
      acyclicOnDecidable B hs (fun i => vertices i ∧ 0<B r i)
    have d0 : Decidable (SkewSymmetric B) := inferInstance
    have d1 : Decidable (vertices r) := inferInstance
    have d2 : Decidable (¬ AcyclicOn B vertices) := inferInstance
    have d3 : Decidable (∀ i j, vertices i → vertices j → i≠j → 2≤(B i j).natAbs) := inferInstance
    have d4 : Decidable (AcyclicOn B (fun i => vertices i ∧ 0<B i r)) := inferInstance
    have d5 : Decidable (AcyclicOn B (fun i => vertices i ∧ 0<B r i)) := inferInstance
    have d6 : Decidable (∀ i j, vertices i → vertices j → 0<B i r → 0<B r j → B i r < B j i ∧ B r j < B j i) := inferInstance
    unfold ForkOnChecks
    exact @instDecidableAnd _ _ d0 (@instDecidableAnd _ _ d1 (@instDecidableAnd _ _ d2 (@instDecidableAnd _ _ d3 (@instDecidableAnd _ _ d4 (@instDecidableAnd _ _ d5 d6)))))
  · exact isFalse (fun h => hs h.1)

instance (B : Matrix 4) (r : Fin 4) (vertices : Fin 4 → Prop) [DecidablePred vertices] :
    Decidable (ForkOnChecks B r vertices) :=
  cachedDecidable (fun C => ForkOnChecks C r vertices)
    (fun C => forkOnChecksDecidable C r vertices) B


def Stopover (B : Matrix 4) (s t v : Fin 4) : Prop :=
  (0<B s v ∧ 0<B v t) ∨ (0<B t v ∧ 0<B v s)
instance (B : Matrix 4) (s t v : Fin 4) : Decidable (Stopover B s t v) := by
  unfold Stopover; infer_instance

/-- Initial `check_prefork`, with the supplied special pair and weak weight. -/
def PreforkChecks (B : Matrix 4) (r s t : Fin 4) (weight : Nat) : Prop :=
  s<t ∧ r≠s ∧ r≠t ∧ (B s t).natAbs=weight ∧
  (∀ v, ¬Stopover B s t v) ∧
  ForkOnChecks B r (fun i => i≠s) ∧ ForkOnChecks B r (fun i => i≠t)
instance (B : Matrix 4) (r s t : Fin 4) (weight : Nat) :
    Decidable (PreforkChecks B r s t weight) := by
  unfold PreforkChecks; infer_instance

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
private theorem large_cases (x : Int) (h : 2≤x.natAbs) : 2≤x ∨ x≤-2 := by
  by_cases hx : 0≤x
  · have := Int.natAbs_of_nonneg hx; left; omega
  · have := Int.ofNat_natAbs_of_nonpos (show x≤0 by omega); right; omega

/-- The full-matrix raw fork check is precisely strong enough for the existing
universal fork continuation theorem. -/
theorem forkOn_full_sound (B : Matrix 4) (r : Fin 4)
    (h : ForkOnChecks B r (fun _ => True)) : Forks.IsFork B r := by
  obtain ⟨hs,_,hc,ha,hin,hout,hcross⟩ := h
  apply graphFork_to_framed B r
  refine ⟨hs,?_,fun i j hij => ha i j trivial trivial hij,?_,?_,?_⟩
  · rintro ⟨rank,hr⟩
    exact hc ⟨rank,fun i j _ _ he => hr i j he⟩
  · obtain ⟨rank,hr⟩ := hin
    exact ⟨rank,fun i j hi hj he => hr i j ⟨trivial,hi⟩ ⟨trivial,hj⟩ he⟩
  · obtain ⟨rank,hr⟩ := hout
    exact ⟨rank,fun i j hi hj he => hr i j ⟨trivial,hi⟩ ⟨trivial,hj⟩ he⟩
  · exact fun i j hi hj => hcross i j trivial trivial hi hj

private theorem prefork_zero_shape (a b c d e f : Int)
    (hs : ForkOnChecks (ofSix a b c d e f) 0 (fun i => i≠2))
    (ht : ForkOnChecks (ofSix a b c d e f) 0 (fun i => i≠3)) :
    Regions.Domain a d e (-b) (-c) ∨ Regions.Domain (-a) (-d) (-e) b c := by
  obtain ⟨hsk,_,hcycS,habundS,hinS,houtS,hcrossS⟩ := hs
  obtain ⟨_,_,hcycT,habundT,hinT,houtT,hcrossT⟩ := ht
  have ha := large_cases a (habundS 0 1 (by decide) (by decide) (by decide))
  have hb := large_cases b (habundT 0 2 (by decide) (by decide) (by decide))
  have hc := large_cases c (habundS 0 3 (by decide) (by decide) (by decide))
  have hd := large_cases d (habundT 1 2 (by decide) (by decide) (by decide))
  have he := large_cases e (habundS 1 3 (by decide) (by decide) (by decide))
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc with hc|hc <;>
    rcases hd with hd|hd <;> rcases he with he|he
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycT
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycT
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · have hd := hcrossT 2 1 (by decide) (by decide) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have he := hcrossS 3 1 (by decide) (by decide) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    left
    simp only [ofSix] at hd he
    unfold Regions.Domain
    omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycT
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycT
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · have hd := hcrossT 1 2 (by decide) (by decide) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    have he := hcrossS 1 3 (by decide) (by decide) (by simp [ofSix]; omega) (by simp [ofSix]; omega)
    right
    simp only [ofSix] at hd he
    unfold Regions.Domain
    omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycT
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 2),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycT
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 0 | _ => 1),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega
  · exfalso
    apply hcycS
    refine ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 0),?_⟩
    intro i j hi hj hij
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [ofSix] at hi hj hij ⊢ <;> omega

/-- Raw induced fork checks commute with arbitrary relabeling. -/
theorem forkOn_relabel (B : Matrix 4) (r : Fin 4) (S : Fin 4 → Prop)
    (h : ForkOnChecks B r S) (p : Relabeling 4) :
    ForkOnChecks (relabel B p) (p.invFun r) (fun i => S (p.toFun i)) := by
  obtain ⟨hs,hr,hc,ha,⟨ri,hi⟩,⟨ro,ho⟩,hx⟩ := h
  refine ⟨relabel_skew B p hs,?_,?_,?_,?_,?_,?_⟩
  · simpa only [p.right_inv] using hr
  · rintro ⟨rank,ht⟩
    apply hc
    refine ⟨rank ∘ p.invFun,?_⟩
    intro i j hsi hsj hij
    exact ht (p.invFun i) (p.invFun j)
      (by simpa only [p.right_inv] using hsi)
      (by simpa only [p.right_inv] using hsj)
      (by simpa only [relabel,p.right_inv] using hij)
  · exact fun i j hi hj hij => ha _ _ hi hj (fun he => hij (p.injective he))
  · refine ⟨ri ∘ p.toFun,?_⟩
    intro i j hsi hsj hij
    simp only [relabel,p.right_inv] at hsi hsj hij
    exact hi _ _ hsi hsj hij
  · refine ⟨ro ∘ p.toFun,?_⟩
    intro i j hsi hsj hij
    simp only [relabel,p.right_inv] at hsi hsj hij
    exact ho _ _ hsi hsj hij
  · intro i j hi hj hir hrj
    simp only [relabel,p.right_inv] at hir hrj ⊢
    exact hx _ _ hi hj hir hrj

private theorem root_of_signed_domain (a b c d e f : Int)
    (h : Regions.Domain a d e (-b) (-c)) (hf : f=0 ∨ f=1 ∨ f = -1) :
    Regions.IsRoot (ofSix a b c d e f) 0 := by
  rcases hf with rfl|rfl|rfl
  · have he : ofSix a b c d e 0 = Regions.root a d e (-b) (-c) 0 := by
      unfold Regions.root; simp only [Int.neg_neg]
    rw [he]
    exact .basic _ _ _ _ _ _ h (Or.inl rfl)
  · have he : ofSix a b c d e 1 = Regions.root a d e (-b) (-c) 1 := by
      unfold Regions.root; simp only [Int.neg_neg]
    rw [he]
    exact .basic _ _ _ _ _ _ h (Or.inr rfl)
  · have he : relabel (ofSix a b c d e (-1)) Regions.frame0132 =
        Regions.root a e d (-c) (-b) 1 := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [relabel,Regions.frame0132,Regions.root,ofSix]
    have hd : Regions.Domain a e d (-c) (-b) := by unfold Regions.Domain at *; omega
    have hr : Regions.IsRoot (relabel (ofSix a b c d e (-1)) Regions.frame0132) 0 := by
      rw [he]; exact .basic _ _ _ _ _ _ hd (Or.inr rfl)
    exact Regions.root_of_relabel Regions.frame0132 hr

private theorem normalized_prefork_sound (a b c d e f : Int)
    (hs : ForkOnChecks (ofSix a b c d e f) 0 (fun i => i≠2))
    (ht : ForkOnChecks (ofSix a b c d e f) 0 (fun i => i≠3))
    (hf : f=0 ∨ f=1 ∨ f = -1) : Regions.IsRoot (ofSix a b c d e f) 0 := by
  rcases prefork_zero_shape a b c d e f hs ht with h|h
  · exact root_of_signed_domain a b c d e f h hf
  · have he : reverse (ofSix a b c d e f) = ofSix (-a) (-b) (-c) (-d) (-e) (-f) := by
      funext i j
      rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
        simp [reverse,ofSix]
    apply Regions.root_of_reverse
    rw [he]
    apply root_of_signed_domain
    · simpa only [Int.neg_neg] using h
    · rcases hf with hf|hf|hf <;> omega

/-- The supplied labels determine a coordinate frame; parameters are extracted
from the actual raw matrix, never supplied as an extra certificate witness. -/
theorem preforkChecks_sound (B : Matrix 4) (r s t : Fin 4) (weight : Nat)
    (hw : weight=0 ∨ weight=1) (h : PreforkChecks B r s t weight) : Regions.IsRoot B r := by
  obtain ⟨hst,hrs,hrt,hedge,_,hs,ht⟩ := h
  have hne : s≠t := by omega
  obtain ⟨i,hir,his,hit⟩ := (show ∀ r s t : Fin 4, r≠s → r≠t → s≠t →
    ∃ i : Fin 24, (Census.permutation i).toFun 0=r ∧
      (Census.permutation i).toFun 2=s ∧ (Census.permutation i).toFun 3=t by decide) r s t hrs hrt hne
  let p := Census.permutation i
  have hp0 : p.invFun r=0 := by rw [←hir]; exact p.left_inv 0
  have hp2 : (fun j => p.toFun j≠s)=(fun j : Fin 4 => j≠2) := by
    funext j
    apply propext
    rw [←his]
    exact not_congr ⟨p.injective,congrArg p.toFun⟩
  have hp3 : (fun j => p.toFun j≠t)=(fun j : Fin 4 => j≠3) := by
    funext j
    apply propext
    rw [←hit]
    exact not_congr ⟨p.injective,congrArg p.toFun⟩
  have hs' := forkOn_relabel B r (fun j => j≠s) hs p
  have ht' := forkOn_relabel B r (fun j => j≠t) ht p
  rw [hp0,hp2] at hs'
  rw [hp0,hp3] at ht'
  have hsk := relabel_skew B p hs.1
  have he := ofSix_reconstruct (relabel B p) hsk
  rw [←he] at hs' ht'
  have hf : relabel B p 2 3=0 ∨ relabel B p 2 3=1 ∨ relabel B p 2 3 = -1 := by
    have hh : (relabel B p 2 3).natAbs=weight := by
      simpa only [relabel,show p.toFun 2=s from his,show p.toFun 3=t from hit] using hedge
    rcases hw with rfl|rfl
    · left; omega
    · right
      by_cases hx : 0≤relabel B p 2 3
      · have hn := Int.natAbs_of_nonneg hx; left; omega
      · have hn := Int.ofNat_natAbs_of_nonpos (show relabel B p 2 3≤0 by omega); right; omega
  have hr := normalized_prefork_sound _ _ _ _ _ _ hs' ht' hf
  rw [he] at hr
  have hout := Regions.root_of_relabel p hr
  simpa only [show p.toFun 0=r from hir] using hout

/-- Equality of all entries, the matrix-equality test used by the verifier. -/
def BoundaryMatrixEq (B C : Matrix 4) : Prop := ∀ i j, B i j=C i j
instance (B C : Matrix 4) : Decidable (BoundaryMatrixEq B C) :=
  inferInstanceAs (Decidable (∀ i j, B i j=C i j))

def WingChecks (B : Matrix 4) (r s t : Fin 4) : Prop :=
  s<t ∧ (r=s ∨ r=t) ∧ B s t=0 ∧
  (∀ v, Stopover B s t v ↔ v≠s ∧ v≠t) ∧
  ForkOnChecks B r (fun i => i≠(if r=s then t else s)) ∧
  FiniteAcyclic (mask B (fun i => i≠r)) ∧
  ∀ i j, i≠r → j≠r → i≠j → 2≤(B i j).natAbs
instance (B : Matrix 4) (r s t : Fin 4) : Decidable (WingChecks B r s t) := by
  unfold WingChecks; infer_instance

def TipChecks (B : Matrix 4) (s t : Fin 4) : Prop :=
  s<t ∧ B s t=0 ∧ (∀ v, ¬Stopover B s t v) ∧
  ForkOnChecks B s (fun i => i≠t) ∧ ForkOnChecks B t (fun i => i≠s)
instance (B : Matrix 4) (s t : Fin 4) : Decidable (TipChecks B s t) := by
  unfold TipChecks; infer_instance

/-- All 16 choices replayed by Python's `check_diamond_cell`, including
commutation, both inward transitions and each exterior boundary check. -/
def DiamondCellChecks (B : Matrix 4) (r s t : Fin 4) : Prop :=
  PreforkChecks B r s t 0 ∧
  (∀ x, x=s ∨ x=t → WingChecks (mutate B x) x s t ∧
    BoundaryMatrixEq (mutate (mutate B x) x) B ∧
    ∀ k, k≠s → k≠t → ForkOnChecks (mutate (mutate B x) k) k (fun _ => True)) ∧
  BoundaryMatrixEq (mutate (mutate B s) t) (mutate (mutate B t) s) ∧
  TipChecks (mutate (mutate B s) t) s t ∧
  BoundaryMatrixEq (mutate (mutate (mutate B s) t) s) (mutate B t) ∧
  BoundaryMatrixEq (mutate (mutate (mutate B s) t) t) (mutate B s) ∧
  (∀ k, k≠s → k≠t → PreforkChecks (mutate (mutate (mutate B s) t) k) k s t 0) ∧
  ∀ k, k≠s → k≠t → k≠r → PreforkChecks (mutate B k) k s t 0
private def CachedDiamondCellChecks (B : Matrix 4) (r s t : Fin 4) : Prop :=
  PreforkChecks B r s t 0 ∧
  (∀ x, x=s ∨ x=t → WingChecks (cachedMutate B x) x s t ∧
    BoundaryMatrixEq (cachedMutate (cachedMutate B x) x) B ∧
    ∀ k, k≠s → k≠t → ForkOnChecks (cachedMutate (cachedMutate B x) k) k (fun _ => True)) ∧
  BoundaryMatrixEq (cachedMutate (cachedMutate B s) t) (cachedMutate (cachedMutate B t) s) ∧
  TipChecks (cachedMutate (cachedMutate B s) t) s t ∧
  BoundaryMatrixEq (cachedMutate (cachedMutate (cachedMutate B s) t) s) (cachedMutate B t) ∧
  BoundaryMatrixEq (cachedMutate (cachedMutate (cachedMutate B s) t) t) (cachedMutate B s) ∧
  (∀ k, k≠s → k≠t → PreforkChecks (cachedMutate (cachedMutate (cachedMutate B s) t) k) k s t 0) ∧
  ∀ k, k≠s → k≠t → k≠r → PreforkChecks (cachedMutate B k) k s t 0
private instance (B : Matrix 4) (r s t : Fin 4) : Decidable (CachedDiamondCellChecks B r s t) := by
  unfold CachedDiamondCellChecks; infer_instance
instance (B : Matrix 4) (r s t : Fin 4) : Decidable (DiamondCellChecks B r s t) :=
  decidable_of_iff (CachedDiamondCellChecks B r s t)
    (by simp only [CachedDiamondCellChecks,DiamondCellChecks,cachedMutate_eq])

def boundarySwap (s t v : Fin 4) : Fin 4 := if v=s then t else if v=t then s else v
def boundarySwapped (B : Matrix 4) (s t : Fin 4) : Matrix 4 :=
  fun i j => B (boundarySwap s t i) (boundarySwap s t j)
def ringLabel (s t : Fin 4) (n : Nat) : Fin 4 := if n%2=0 then s else t

def unitRing (B : Matrix 4) (s t : Fin 4) : Nat → Matrix 4
  | 0 => B
  | n+1 => mutate (unitRing B s t n) (ringLabel s t n)

/-- Pass each materialized state to its successor before exposing entries. -/
@[noinline] private def withRing {α : Type} (B : Matrix 4) (s t : Fin 4) :
    Nat → (Matrix 4 → α) → α
  | 0, next => withSnapshot B next
  | n+1, next => withRing B s t n (fun C =>
      withSnapshot (mutate C (ringLabel s t n)) next)

private theorem withRing_eq {α : Type} (B : Matrix 4) (s t : Fin 4)
    (n : Nat) (next : Matrix 4 → α) :
    withRing B s t n next = next (unitRing B s t n) := by
  induction n generalizing next with
  | zero => simp only [withRing,withSnapshot_eq,unitRing]
  | succ n ih => simp only [withRing,ih,withSnapshot_eq,unitRing]

/-- Materialize each ring state before its next mutation. -/
def cachedRing (B : Matrix 4) (s t : Fin 4) (n : Nat) : Matrix 4 :=
  withRing B s t n (fun C => C)

theorem cachedRing_eq (B : Matrix 4) (s t : Fin 4) (n : Nat) :
    cachedRing B s t n = unitRing B s t n := by
  exact withRing_eq B s t n (fun C => C)

def ringDistance (n : Nat) : Nat := min n (min ((n-5)+(5-n)) (10-n))

def RingInward (r s t : Fin 4) (n : Nat) (k : Fin 4) : Prop :=
  if n=0 ∨ n=5 then k=r else
    (k=ringLabel s t (n+1) ∧ ringDistance ((n+9)%10)<ringDistance n) ∨
    (k=ringLabel s t n ∧ ringDistance ((n+1)%10)<ringDistance n)
instance (r s t : Fin 4) (n : Nat) (k : Fin 4) : Decidable (RingInward r s t n k) := by
  unfold RingInward; infer_instance

def CyclicTriangleCheck (B : Matrix 4) (i j k : Fin 4) : Prop :=
  (0<B i j ∧ 0<B j k ∧ 0<B k i) ∨ (B i j<0 ∧ B j k<0 ∧ B k i<0)
instance (B : Matrix 4) (i j k : Fin 4) : Decidable (CyclicTriangleCheck B i j k) := by
  unfold CyclicTriangleCheck; infer_instance

/-- Exact per-state unit-decagon replay, including the inward-triangle test. -/
def UnitStateChecks (B : Matrix 4) (r s t : Fin 4) (n : Fin 10) : Prop :=
  ¬FiniteAcyclic (unitRing B s t n.val) ∧
  ((unitRing B s t n.val) s t).natAbs=1 ∧
  (∀ i j, i<j → ¬(i=s ∧ j=t) → 2≤((unitRing B s t n.val) i j).natAbs) ∧
  BoundaryMatrixEq (mutate (unitRing B s t n.val) (ringLabel s t (n.val+1)))
    (unitRing B s t ((n.val+9)%10)) ∧
  BoundaryMatrixEq (mutate (unitRing B s t n.val) (ringLabel s t n.val))
    (unitRing B s t ((n.val+1)%10)) ∧
  (∃ k, RingInward r s t n.val k) ∧
  (∀ i j k, i<j → j<k → CyclicTriangleCheck (unitRing B s t n.val) i j k →
    RingInward r s t n.val i ∨ RingInward r s t n.val j ∨ RingInward r s t n.val k) ∧
  ∀ k, k≠s → k≠t → ¬((n.val=0 ∨ n.val=5) ∧ k=r) →
    ForkOnChecks (mutate (unitRing B s t n.val) k) k (fun _ => True) ∨
      PreforkChecks (mutate (unitRing B s t n.val) k) k s t 1
private def CachedUnitStateChecks (B : Matrix 4) (r s t : Fin 4) (n : Fin 10) : Prop :=
  ¬FiniteAcyclic (cachedRing B s t n.val) ∧
  ((cachedRing B s t n.val) s t).natAbs=1 ∧
  (∀ i j, i<j → ¬(i=s ∧ j=t) → 2≤((cachedRing B s t n.val) i j).natAbs) ∧
  BoundaryMatrixEq (cachedMutate (cachedRing B s t n.val) (ringLabel s t (n.val+1)))
    (cachedRing B s t ((n.val+9)%10)) ∧
  BoundaryMatrixEq (cachedMutate (cachedRing B s t n.val) (ringLabel s t n.val))
    (cachedRing B s t ((n.val+1)%10)) ∧
  (∃ k, RingInward r s t n.val k) ∧
  (∀ i j k, i<j → j<k → CyclicTriangleCheck (cachedRing B s t n.val) i j k →
    RingInward r s t n.val i ∨ RingInward r s t n.val j ∨ RingInward r s t n.val k) ∧
  ∀ k, k≠s → k≠t → ¬((n.val=0 ∨ n.val=5) ∧ k=r) →
    ForkOnChecks (cachedMutate (cachedRing B s t n.val) k) k (fun _ => True) ∨
      PreforkChecks (cachedMutate (cachedRing B s t n.val) k) k s t 1
private def UnitStateAtChecks (B C : Matrix 4) (r s t : Fin 4) (n : Fin 10) : Prop :=
  ¬FiniteAcyclic C ∧
  (C s t).natAbs=1 ∧
  (∀ i j, i<j → ¬(i=s ∧ j=t) → 2≤(C i j).natAbs) ∧
  BoundaryMatrixEq (cachedMutate C (ringLabel s t (n.val+1)))
    (cachedRing B s t ((n.val+9)%10)) ∧
  BoundaryMatrixEq (cachedMutate C (ringLabel s t n.val))
    (cachedRing B s t ((n.val+1)%10)) ∧
  (∃ k, RingInward r s t n.val k) ∧
  (∀ i j k, i<j → j<k → CyclicTriangleCheck C i j k →
    RingInward r s t n.val i ∨ RingInward r s t n.val j ∨ RingInward r s t n.val k) ∧
  ∀ k, k≠s → k≠t → ¬((n.val=0 ∨ n.val=5) ∧ k=r) →
    ForkOnChecks (cachedMutate C k) k (fun _ => True) ∨
      PreforkChecks (cachedMutate C k) k s t 1
private instance (B C : Matrix 4) (r s t : Fin 4) (n : Fin 10) :
    Decidable (UnitStateAtChecks B C r s t n) := by
  unfold UnitStateAtChecks; infer_instance
private instance (B : Matrix 4) (r s t : Fin 4) (n : Fin 10) :
    Decidable (CachedUnitStateChecks B r s t n) :=
  decidable_of_iff
    (withRing B s t n.val (fun C => decide (UnitStateAtChecks B C r s t n)) = true)
    (by simp only [withRing_eq,decide_eq_true_eq,UnitStateAtChecks,
      CachedUnitStateChecks,cachedRing_eq])

instance (B : Matrix 4) (r s t : Fin 4) (n : Fin 10) : Decidable (UnitStateChecks B r s t n) :=
  decidable_of_iff (CachedUnitStateChecks B r s t n)
    (by simp only [CachedUnitStateChecks,UnitStateChecks,cachedRing_eq,cachedMutate_eq])

/-- Every clause of `check_unit_cell`: the ten-step closure, swapped midpoint,
second return, all forty mutation choices, and inward tests. -/
def UnitCellChecks (B : Matrix 4) (r s t : Fin 4) : Prop :=
  PreforkChecks B r s t 1 ∧
  BoundaryMatrixEq (unitRing B s t 10) B ∧
  BoundaryMatrixEq (unitRing B s t 5) (boundarySwapped B s t) ∧
  BoundaryMatrixEq (mutate (unitRing B s t 5) r) (boundarySwapped (mutate B r) s t) ∧
  ∀ n : Fin 10, UnitStateChecks B r s t n
private def CachedUnitCellChecks (B : Matrix 4) (r s t : Fin 4) : Prop :=
  PreforkChecks B r s t 1 ∧
  BoundaryMatrixEq (cachedRing B s t 10) B ∧
  BoundaryMatrixEq (cachedRing B s t 5) (boundarySwapped B s t) ∧
  BoundaryMatrixEq (cachedMutate (cachedRing B s t 5) r) (boundarySwapped (cachedMutate B r) s t) ∧
  ∀ n : Fin 10, UnitStateChecks B r s t n
private instance (B : Matrix 4) (r s t : Fin 4) : Decidable (CachedUnitCellChecks B r s t) := by
  unfold CachedUnitCellChecks; infer_instance
instance (B : Matrix 4) (r s t : Fin 4) : Decidable (UnitCellChecks B r s t) :=
  decidable_of_iff (CachedUnitCellChecks B r s t)
    (by simp only [CachedUnitCellChecks,UnitCellChecks,cachedRing_eq,cachedMutate_eq])

/-- The raw Python L0 grammar: matrix, return, kind, and optional special pair. -/
def BoundaryChecks (record : BoundaryRecord) : Prop :=
  match record.kind with
  | .fork => ForkOnChecks record.quiver.matrix record.returnVertex (fun _ => True)
  | .diamond s t => DiamondCellChecks record.quiver.matrix record.returnVertex s t
  | .unit s t => UnitCellChecks record.quiver.matrix record.returnVertex s t
instance (record : BoundaryRecord) : Decidable (BoundaryChecks record) := by
  unfold BoundaryChecks; split <;> infer_instance

def checkBoundary (record : BoundaryRecord) : Bool := decide (BoundaryChecks record)

theorem checkBoundary_iff (record : BoundaryRecord) :
    checkBoundary record=true ↔ BoundaryChecks record := by
  simp only [checkBoundary,decide_eq_true_eq]

/-- Accepted raw boundaries have the exact proved structural continuation
predicate; normalization is derived rather than supplied in the record. -/
theorem boundaryChecks_sound (record : BoundaryRecord) (h : BoundaryChecks record) :
    Forks.IsFork record.quiver.matrix record.returnVertex ∨
      Regions.IsRoot record.quiver.matrix record.returnVertex := by
  cases hk : record.kind with
  | fork => exact Or.inl (forkOn_full_sound _ _ (by simpa only [BoundaryChecks,hk] using h))
  | diamond s t =>
    have hd : DiamondCellChecks record.quiver.matrix record.returnVertex s t := by
      simpa only [BoundaryChecks,hk] using h
    exact Or.inr (preforkChecks_sound _ _ _ _ 0 (Or.inl rfl) hd.1)
  | unit s t =>
    have hu : UnitCellChecks record.quiver.matrix record.returnVertex s t := by
      simpa only [BoundaryChecks,hk] using h
    exact Or.inr (preforkChecks_sound _ _ _ _ 1 (Or.inr rfl) hu.1)


end QuiverProofs.LStar
