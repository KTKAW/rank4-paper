import QuiverProofs.RegionCells

/-! A computable normalized finite-region certificate checker and a fair
finite-stage certificate search. The checker works on typed Lean records;
no equivalence with the external JSON parser or Python verifier is asserted.
The search termination theorem exposes its covering/fairness assumptions. -/
namespace QuiverProofs.CertificateSearch

def EntriesEqual (B C : Matrix 4) : Prop := ∀ i j, B i j = C i j
instance (B C : Matrix 4) : Decidable (EntriesEqual B C) :=
  inferInstanceAs (Decidable (∀ i j, B i j = C i j))
theorem entriesEqual_eq {B C : Matrix 4} (h : EntriesEqual B C) : B=C := by
  funext i j; exact h i j

def transport (B : Matrix 4) (p : Relabeling 4) (flip : Bool) : Matrix 4 :=
  relabel (if flip then reverse B else B) p

structure ForkRecord where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  frame : Relabeling 4
  flip : Bool

def ForkChecks (record : ForkRecord) (B : Matrix 4) (r : Fin 4) : Prop :=
  Forks.Domain record.a record.b record.c record.d record.e record.f ∧
    EntriesEqual B (transport (Forks.template record.a record.b record.c record.d record.e record.f)
      record.frame record.flip) ∧ r=record.frame.invFun 0
instance (record : ForkRecord) (B : Matrix 4) (r : Fin 4) : Decidable (ForkChecks record B r) := by
  unfold ForkChecks Forks.Domain
  infer_instance

theorem forkChecks_sound (record : ForkRecord) (B : Matrix 4) (r : Fin 4)
    (h : ForkChecks record B r) : Forks.IsFork B r := by
  obtain ⟨hd,he,hr⟩ := h
  rw [entriesEqual_eq he,hr]
  have hf := Forks.IsFork.basic _ _ _ _ _ _ hd
  cases hflip : record.flip
  · simpa only [transport,hflip,Bool.false_eq_true,↓reduceIte] using Forks.IsFork.relabelled hf record.frame
  · simpa only [transport,hflip,↓reduceIte] using Forks.IsFork.relabelled (Forks.IsFork.reversed hf) record.frame

structure RootRecord where
  A : Int
  B : Int
  C : Int
  D : Int
  E : Int
  ε : Int
  frame : Relabeling 4
  flip : Bool

def RootChecks (record : RootRecord) (B : Matrix 4) (r : Fin 4) : Prop :=
  Regions.Domain record.A record.B record.C record.D record.E ∧ (record.ε=0 ∨ record.ε=1) ∧
    EntriesEqual B (transport (Regions.root record.A record.B record.C record.D record.E record.ε)
      record.frame record.flip) ∧ r=record.frame.invFun 0
instance (record : RootRecord) (B : Matrix 4) (r : Fin 4) : Decidable (RootChecks record B r) := by
  unfold RootChecks Regions.Domain
  infer_instance

theorem rootChecks_sound (record : RootRecord) (B : Matrix 4) (r : Fin 4)
    (h : RootChecks record B r) : Regions.IsRoot B r := by
  obtain ⟨hd,hε,he,hr⟩ := h
  rw [entriesEqual_eq he,hr]
  have hf := Regions.IsRoot.basic _ _ _ _ _ _ hd hε
  cases hflip : record.flip
  · simpa only [transport,hflip,Bool.false_eq_true,↓reduceIte] using Regions.IsRoot.relabelled hf record.frame
  · simpa only [transport,hflip,↓reduceIte] using Regions.IsRoot.relabelled (Regions.IsRoot.reversed hf) record.frame

inductive CycleRecord where
  | triangle (i j k : Fin 4)
  | square (i j k l : Fin 4)

def CycleChecks (record : CycleRecord) (B : Matrix 4) : Prop :=
  match record with
  | .triangle i j k => 0<B i j ∧ 0<B j k ∧ 0<B k i
  | .square i j k l => 0<B i j ∧ 0<B j k ∧ 0<B k l ∧ 0<B l i
instance (record : CycleRecord) (B : Matrix 4) : Decidable (CycleChecks record B) := by
  cases record <;> unfold CycleChecks <;> infer_instance

theorem cycleChecks_sound (record : CycleRecord) (B : Matrix 4)
    (h : CycleChecks record B) : ¬ Acyclic B := by
  rintro ⟨rank,hr⟩
  cases record with
  | triangle i j k =>
    have h1 := hr i j h.1
    have h2 := hr j k h.2.1
    have h3 := hr k i h.2.2
    omega
  | square i j k l =>
    have h1 := hr i j h.1
    have h2 := hr j k h.2.1
    have h3 := hr k l h.2.2.1
    have h4 := hr l i h.2.2.2
    omega

inductive EdgeRecord (size : Nat) where
  | internal (target : Fin size) (frame : Relabeling 4)
  | fork (record : ForkRecord)
  | root (record : RootRecord)

def EdgeChecks {size : Nat} (nodes : Fin size → Matrix 4) (i : Fin size)
    (k : Fin 4) (edge : EdgeRecord size) : Prop :=
  match edge with
  | .internal j p => EntriesEqual (mutate (nodes i) k) (relabel (nodes j) p)
  | .fork record => ForkChecks record (mutate (nodes i) k) k
  | .root record => RootChecks record (mutate (nodes i) k) k
instance {size : Nat} (nodes : Fin size → Matrix 4) (i : Fin size)
    (k : Fin 4) (edge : EdgeRecord size) : Decidable (EdgeChecks nodes i k edge) := by
  cases edge <;> unfold EdgeChecks <;> infer_instance

theorem edgeChecks_sound {size : Nat} (nodes : Fin size → Matrix 4) (i : Fin size)
    (k : Fin 4) (edge : EdgeRecord size) (h : EdgeChecks nodes i k edge) :
    Forks.FramedCore nodes (mutate (nodes i) k) ∨
      Forks.IsFork (mutate (nodes i) k) k ∨ Regions.IsRoot (mutate (nodes i) k) k := by
  cases edge with
  | internal j p => exact Or.inl ⟨j,p,entriesEqual_eq h⟩
  | fork record => exact Or.inr (Or.inl (forkChecks_sound record _ _ h))
  | root record => exact Or.inr (Or.inr (rootChecks_sound record _ _ h))

structure RegionCertificate where
  size : Nat
  root : Fin size
  node : Fin size → Matrix 4
  cycle : Fin size → CycleRecord
  edge : Fin size → Fin 4 → EdgeRecord size
  entry : List (Fin 4)

def CertificateChecks (B : Matrix 4) (c : RegionCertificate) : Prop :=
  EntriesEqual (applyWord B c.entry) (c.node c.root) ∧
    (∀ i, SkewSymmetric (c.node i)) ∧
    (∀ i, CycleChecks (c.cycle i) (c.node i)) ∧
    ∀ i k, EdgeChecks c.node i k (c.edge i k)
instance (B : Matrix 4) (c : RegionCertificate) : Decidable (CertificateChecks B c) := by
  unfold CertificateChecks SkewSymmetric
  infer_instance

def acceptCertificate (B : Matrix 4) (c : RegionCertificate) : Bool :=
  decide (CertificateChecks B c)

theorem acceptCertificate_iff (B : Matrix 4) (c : RegionCertificate) :
    acceptCertificate B c = true ↔ CertificateChecks B c := by
  simp only [acceptCertificate,decide_eq_true_eq]

theorem acceptCertificate_NMA (B : Matrix 4) (c : RegionCertificate)
    (h : acceptCertificate B c = true) : ¬ MutationAcyclic B := by
  obtain ⟨he,hs,hcyc,hedge⟩ := (acceptCertificate_iff B c).mp h
  have hn := RegionSemantics.framed_region_NMA RegionCells.root_cells_exist c.node hs
    (fun i => cycleChecks_sound (c.cycle i) _ (hcyc i))
    (fun i k => edgeChecks_sound c.node i k (c.edge i k) (hedge i k)) c.root
  intro hMA
  apply hn
  rw [← entriesEqual_eq he]
  exact (mutationAcyclic_word_iff B c.entry).mpr hMA

/-- A finite stage is executable; exhausting a stage returns `none`. -/
def searchStage {Witness : Type} (accept : Witness → Bool) : List Witness → Option Witness
  | [] => none
  | w::ws => if accept w then some w else searchStage accept ws

theorem searchStage_some_accepted {Witness : Type} (accept : Witness → Bool)
    (candidates : List Witness) (w : Witness) (h : searchStage accept candidates = some w) :
    w∈candidates ∧ accept w=true := by
  induction candidates with
  | nil => simp [searchStage] at h
  | cons x xs ih =>
    by_cases hx : accept x=true
    · simp only [searchStage,hx,↓reduceIte,Option.some.injEq] at h
      subst w; exact ⟨by simp,hx⟩
    · have hn : accept x=false := by cases he : accept x <;> simp_all
      simp only [searchStage,hn,Bool.false_eq_true,↓reduceIte] at h
      obtain ⟨hw,ha⟩ := ih h
      exact ⟨by simp [hw],ha⟩

theorem searchStage_finds {Witness : Type} (accept : Witness → Bool)
    (candidates : List Witness) (w : Witness) (hw : w∈candidates) (ha : accept w=true) :
    ∃ result, searchStage accept candidates = some result := by
  induction candidates with
  | nil => simp at hw
  | cons x xs ih =>
    by_cases hx : accept x=true
    · exact ⟨x,by simp [searchStage,hx]⟩
    · have hn : accept x=false := by cases he : accept x <;> simp_all
      have hw' : w∈xs := by rcases List.mem_cons.mp hw with rfl|hh; exact False.elim (hx ha); exact hh
      obtain ⟨result,hr⟩ := ih hw'
      exact ⟨result,by simp [searchStage,hn,hr]⟩

/-- Conditional termination of a fair finite-stage search. `cover` says an
accepted finite witness exists; `fair` states that every witness is scheduled
at a finite stage. Neither assumption is supplied by bounded survival. -/
theorem fair_search_terminates {Witness : Type} (enumerate : Nat → List Witness)
    (accept : Witness → Bool) (fair : ∀ w, ∃ n, w∈enumerate n)
    (cover : ∃ w, accept w=true) :
    ∃ stage result, searchStage accept (enumerate stage) = some result ∧ accept result=true := by
  obtain ⟨w,ha⟩ := cover
  obtain ⟨n,hw⟩ := fair w
  obtain ⟨result,hr⟩ := searchStage_finds accept (enumerate n) w hw ha
  exact ⟨n,result,hr,(searchStage_some_accepted accept (enumerate n) result hr).2⟩

/-- A resource cutoff (`none`) alone has no negative semantic consequence. -/
theorem empty_stage_unresolved {Witness : Type} (accept : Witness → Bool) :
    searchStage accept [] = none := rfl

end QuiverProofs.CertificateSearch
