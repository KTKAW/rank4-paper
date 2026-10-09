import QuiverProofs.MatrixCache
import QuiverProofs.LStarBoundary
import QuiverProofs.LStarDescent
import QuiverProofs.GenericRegionAdapter
import QuiverProofs.UnitRegionRules
import QuiverProofs.CertificateSearch
import QuiverProofs.ForkPruningDecidable
import QuiverProofs.CertificateTransport

/-! Total arithmetic checking of the normalized data-only L-star grammar.
Acceptance establishes the whole-class conclusions using the concrete generic,
unit-zero and unit-pendant region rules. The external Python interpreter is
not modeled here; correspondence with that implementation is a separate claim. -/
namespace QuiverProofs.LStar
open RecursiveRegions TriangleRegions CertificateSearch

def regionData := GenericRegionAdapter.data.sum UnitRegionData.data

def regionRules : RegionRules regionData :=
  GenericRegionAdapter.rules.sum UnitRegionRules.rules

def triangleRules : TriangleRules regionData :=
  GenericRegionAdapter.triangleRules.sum UnitRegionRules.triangleRules

def Base (c : Certificate) (B : Matrix 4) : Prop := ∃ i, B = c.node i

abbrev Safe (c : Certificate) (B : Matrix 4) := RecursiveRegions.Safe regionData (Base c) B

theorem base_skew (c : Certificate) {B : Matrix 4} (h : Base c B) : SkewSymmetric B := by
  obtain ⟨i,rfl⟩ := h
  exact (c.core i).quiver.skew

theorem safe_node (c : Certificate) (i : Fin (c.size+1)) : Safe c (c.node i) :=
  RecursiveRegions.Safe.central ⟨i,rfl⟩

theorem Frame.safe (f : Frame) (c : Certificate) {B : Matrix 4} (h : Safe c B) :
    Safe c (f.apply B) := by
  cases hf : f.flip
  · exact RecursiveRegions.Safe.framed (by simpa only [hf,Bool.false_eq_true,↓reduceIte] using h) f.relabeling
  · exact RecursiveRegions.Safe.framed (by simpa only [hf,↓reduceIte] using RecursiveRegions.Safe.reversed h) f.relabeling

theorem Frame.safe_inverse (f : Frame) (c : Certificate) {B : Matrix 4}
    (h : Safe c (f.apply B)) : Safe c B := by
  have ht := RecursiveRegions.Safe.framed h f.relabeling.symm
  simp only [Frame.apply,relabel_inverse] at ht
  cases hf : f.flip
  · simpa only [hf,Bool.false_eq_true,↓reduceIte] using ht
  · have hr := RecursiveRegions.Safe.reversed ht
    simpa only [hf,↓reduceIte,reverse_involutive] using hr

def StripRecord.phase {size : Nat} (s : StripRecord size) (i : Fin 6) : Matrix 4 :=
  GenericStrip.phase s.m s.a s.b s.c i

def StripRecord.parent {size : Nat} (s : StripRecord size) (p : Fin 3) : Matrix 4 :=
  if p=0 then mutate (s.phase 0) 1 else if p=1 then mutate (s.phase 0) 2 else mutate (s.phase 2) 0

/-- Run the endpoint test while the replayed matrix is materialized. The
continuation returns a Boolean, so compiled evaluation cannot move replay
inside each subsequent entry lookup. -/
def wordEntriesCheck (B : Matrix 4) (word : List (Fin 4))
    (frame : Matrix 4 → Matrix 4) (C : Matrix 4) : Bool :=
  MatrixCache.withWord B word (fun D => decide (EntriesEqual (frame D) C))

theorem wordEntriesCheck_iff (B : Matrix 4) (word : List (Fin 4))
    (frame : Matrix 4 → Matrix 4) (C : Matrix 4) :
    wordEntriesCheck B word frame C = true ↔ EntriesEqual (frame (applyWord B word)) C := by
  simp only [wordEntriesCheck,MatrixCache.withWord_eq,decide_eq_true_eq]

def StripChecks (c : Certificate) (s : StripRecord c.size) : Prop :=
  GenericStrip.Domain s.m s.a s.b s.c ∧
  EntriesEqual s.rootQuiver.matrix (c.node s.rootCore) ∧
  EntriesEqual (applyWord (c.node 0) s.rootWord) (c.node s.rootCore) ∧
  EntriesEqual (s.rootFrame.apply (c.node s.rootCore)) (s.phase 0) ∧
  ∀ p, EntriesEqual ((s.backward p).frame.apply (s.parent p)) (c.node (s.backward p).target)

instance (c : Certificate) (s : StripRecord c.size) : Decidable (StripChecks c s) := by
  haveI : Decidable (GenericStrip.Domain s.m s.a s.b s.c) := by
    unfold GenericStrip.Domain; infer_instance
  exact decidable_of_iff
    (GenericStrip.Domain s.m s.a s.b s.c ∧
     EntriesEqual s.rootQuiver.matrix (c.node s.rootCore) ∧
     wordEntriesCheck (c.node 0) s.rootWord id (c.node s.rootCore) = true ∧
     EntriesEqual (s.rootFrame.apply (c.node s.rootCore)) (s.phase 0) ∧
     ∀ p, EntriesEqual ((s.backward p).frame.apply (s.parent p)) (c.node (s.backward p).target))
    (by simp only [wordEntriesCheck_iff,id_eq]; rfl)

def StripRecord.seed {size : Nat} (s : StripRecord size)
    (h : GenericStrip.Domain s.m s.a s.b s.c) : GenericRegionAdapter.Seed :=
  ⟨s.m,⟨s.a,s.b,s.c⟩,h⟩

theorem strip_safe (c : Certificate) (s : StripRecord c.size) (h : StripChecks c s)
    (i : Fin 6) : Safe c (s.phase i) := by
  let r := s.seed h.1
  have hp : ∀ p, Safe c (GenericRegionAdapter.data.parent r p) := by
    intro p
    change Safe c (s.parent p)
    apply Frame.safe_inverse (s.backward p).frame
    rw [entriesEqual_eq (h.2.2.2.2 p)]
    exact safe_node c _
  exact RecursiveRegions.Safe.region (D := regionData) (core := Base c) (.inl r) hp (0,i)

def zeroRoot (x u v w : Int) (phase : Fin 2) : Matrix 4 :=
  if phase=0 then ofSix 0 (-u) 1 v (-x) w else mutate (ofSix 0 (-u) 1 v (-x) w) 0

def pendantRoot (d x y : Int) (phase : Fin 2) : Matrix 4 :=
  if phase=0 then ofSix 0 0 1 d (-x) y else mutate (ofSix 0 0 1 d (-x) y) 0

def opposite (phase : Fin 2) : Fin 2 := if phase=0 then 1 else 0

def LocalChecks (c : Certificate) (Q : Matrix 4) (k : Fin 4)
    (root : Fin 2 → Matrix 4) (r : LocalRecord c.size) : Prop :=
  r.returnVertex=k ∧ r.frame.relabeling.toFun 1=k ∧
  EntriesEqual (r.frame.apply (mutate Q k)) (root r.phase) ∧
  EntriesEqual (r.frame.apply Q) (mutate (root r.phase) 1) ∧
  EntriesEqual (r.frame.apply (mutate Q (r.frame.relabeling.toFun 0))) (mutate (root (opposite r.phase)) 1) ∧
  EntriesEqual (r.alternateFrame.apply (mutate Q (r.frame.relabeling.toFun 0))) (c.node r.alternateTarget)

instance (c : Certificate) (Q : Matrix 4) (k : Fin 4)
    (root : Fin 2 → Matrix 4) (r : LocalRecord c.size) : Decidable (LocalChecks c Q k root r) := by
  unfold LocalChecks
  infer_instance

theorem local_parents_safe (c : Certificate) (Q : Matrix 4) (hQ : Safe c Q) (k : Fin 4)
    (root : Fin 2 → Matrix 4) (r : LocalRecord c.size) (h : LocalChecks c Q k root r) :
    ∀ p, Safe c (mutate (root p) 1) := by
  have hfirst : Safe c (mutate (root r.phase) 1) := by
    rw [←entriesEqual_eq h.2.2.2.1]
    exact r.frame.safe c hQ
  have halt : Safe c (mutate Q (r.frame.relabeling.toFun 0)) := by
    apply r.alternateFrame.safe_inverse c
    rw [entriesEqual_eq h.2.2.2.2.2]
    exact safe_node c _
  have hsecond : Safe c (mutate (root (opposite r.phase)) 1) := by
    rw [←entriesEqual_eq h.2.2.2.2.1]
    exact r.frame.safe c halt
  intro p
  have hr : r.phase=0 ∨ r.phase=1 := by omega
  have hp : p=0 ∨ p=1 := by omega
  rcases hr with hr|hr <;> rcases hp with rfl|rfl <;>
    simp only [hr,opposite] at hfirst hsecond
  · exact hfirst
  · exact hsecond
  · exact hsecond
  · exact hfirst

theorem unit_entry_safe (c : Certificate) (Q : Matrix 4) (hQ : Safe c Q) (k : Fin 4)
    (root : Fin 2 → Matrix 4) (rec : LocalRecord c.size) (h : LocalChecks c Q k root rec)
    (r : UnitRegionData.Region) (idx : Fin 2 → UnitRegionData.data.Index r)
    (hs : ∀ p, UnitRegionData.data.state r (idx p) = root p)
    (hp : ∀ p, UnitRegionData.data.parent r p = mutate (root p) 1) :
    Safe c (mutate Q k) := by
  apply rec.frame.safe_inverse c
  rw [entriesEqual_eq h.2.2.1]
  rw [←hs]
  change RecursiveRegions.Safe regionData (Base c) (regionData.state (.inr r) (idx rec.phase))
  refine RecursiveRegions.Safe.region (D := regionData) (core := Base c) (.inr r) ?_ (idx rec.phase)
  intro p
  change Safe c (UnitRegionData.data.parent r p)
  rw [hp]
  exact local_parents_safe c Q hQ k root rec h p

theorem zero_state (x u v w : Int) (hd : UnitZeroStrip.Domain x u v w) (p : Fin 2) :
    UnitRegionData.data.state (.n x ⟨u,v,w⟩ hd) (0,Fin.castLE (by decide) p) = zeroRoot x u v w p := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · rfl
  · exact (UnitZeroStrip.special_0 x u v w hd).symm

theorem pendant_state (d x y : Int) (hd : UnitPendantStrip.Domain d x y) (p : Fin 2) :
    UnitRegionData.data.state (.d ⟨d,x,y⟩ hd) (Fin.castLE (by decide) p) = pendantRoot d x y p := by
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · rfl
  · exact (UnitPendantStrip.D0_zero d x y hd).symm

theorem zero_entry_safe (c : Certificate) (Q : Matrix 4) (hQ : Safe c Q) (k : Fin 4)
    (x u v w : Int) (rec : LocalRecord c.size) (hd : UnitZeroStrip.Domain x u v w)
    (h : LocalChecks c Q k (zeroRoot x u v w) rec) : Safe c (mutate Q k) := by
  apply unit_entry_safe c Q hQ k (zeroRoot x u v w) rec h (.n x ⟨u,v,w⟩ hd)
    (fun p => (0,Fin.castLE (by decide) p)) (zero_state x u v w hd)
  intro p
  change Fin 2 at p
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · rfl
  · change mutate (UnitRegionData.data.state (.n x ⟨u,v,w⟩ hd) (0,Fin.castLE (by decide) (1 : Fin 2))) 1 = _
    rw [zero_state]

theorem pendant_entry_safe (c : Certificate) (Q : Matrix 4) (hQ : Safe c Q) (k : Fin 4)
    (d x y : Int) (rec : LocalRecord c.size) (hd : UnitPendantStrip.Domain d x y)
    (h : LocalChecks c Q k (pendantRoot d x y) rec) : Safe c (mutate Q k) := by
  apply unit_entry_safe c Q hQ k (pendantRoot d x y) rec h (.d ⟨d,x,y⟩ hd)
    (fun p => Fin.castLE (by decide) p) (pendant_state d x y hd)
  intro p
  change Fin 2 at p
  have hp : p=0 ∨ p=1 := by omega
  rcases hp with rfl|rfl
  · rfl
  · change mutate (UnitRegionData.data.state (.d ⟨d,x,y⟩ hd) (Fin.castLE (by decide) (1 : Fin 2))) 1 = _
    rw [pendant_state]

end QuiverProofs.LStar

namespace QuiverProofs.LStar
open RecursiveRegions TriangleRegions CertificateSearch

def reachable (B : Matrix 4) : Nat → Fin 4 → Bool
  | 0, i => decide (i=0)
  | n+1, i => reachable B n i || decide (∃ j : Fin 4, reachable B n j = true ∧ B j i ≠ 0)

def ConnectedCheck (B : Matrix 4) : Prop := ∀ i, reachable B 4 i = true
instance (B : Matrix 4) : Decidable (ConnectedCheck B) := by unfold ConnectedCheck; infer_instance

def EdgeChecks (c : Certificate) (i : Fin (c.size+1)) (k : Fin 4)
    (e : EdgeRecord c.size c.stripCount) : Prop :=
  match e with
  | .core j f => EntriesEqual (f.apply (mutate (c.node i) k)) (c.node j)
  | .mstrip s n phase f => n=0 ∧ EntriesEqual (f.apply (mutate (c.node i) k)) ((c.strips s).phase phase)
  | .boundary b => b.returnVertex=k ∧ EntriesEqual b.quiver.matrix (mutate (c.node i) k) ∧
      EntriesEqual (mutate b.quiver.matrix b.returnVertex) (c.node i) ∧ BoundaryChecks b
  | .zero x u v w r => UnitZeroStrip.Domain x u v w ∧ LocalChecks c (c.node i) k (zeroRoot x u v w) r
  | .pendant d x y r => UnitPendantStrip.Domain d x y ∧ LocalChecks c (c.node i) k (pendantRoot d x y) r

instance (c : Certificate) (i : Fin (c.size+1)) (k : Fin 4)
    (e : EdgeRecord c.size c.stripCount) : Decidable (EdgeChecks c i k e) := by
  cases e <;> unfold EdgeChecks
  · infer_instance
  · infer_instance
  · infer_instance
  · unfold UnitZeroStrip.Domain; infer_instance
  · unfold UnitPendantStrip.Domain; infer_instance

/-- Every check is finite arithmetic or quantification over an explicit finite
index type. These propositions add no witnesses to the certificate syntax. -/
structure Checks (c : Certificate) : Prop where
  connected : ConnectedCheck c.initial.matrix
  entry : EntriesEqual (c.entryFrame.apply (applyWord c.initial.matrix c.entryWord)) (c.node 0)
  originWord : (c.core 0).word = []
  reachable : ∀ i, EntriesEqual (applyWord (c.node 0) (c.core i).word) (c.node i)
  cyclic : ∀ i, ¬ ForkPruning.FiniteAcyclic (c.node i)
  strips : ∀ s, StripChecks c (c.strips s)
  edges : ∀ i k, EdgeChecks c i k ((c.core i).edges k)
  triangles : c.triangleAvoidance = decide (∀ i, TriangleDecision.checkAllTrianglesMA (c.node i) = true)
  descents : c.triangleAvoidance = true → ∀ i, allTriangleDescentsCheck (c.node i) = true

instance (c : Certificate) : Decidable (Checks c) :=
  decidable_of_iff
    (ConnectedCheck c.initial.matrix ∧
     wordEntriesCheck c.initial.matrix c.entryWord c.entryFrame.apply (c.node 0) = true ∧
     (c.core 0).word = [] ∧
     (∀ i, wordEntriesCheck (c.node 0) (c.core i).word id (c.node i) = true) ∧
     (∀ i, ¬ ForkPruning.FiniteAcyclic (c.node i)) ∧
     (∀ s, StripChecks c (c.strips s)) ∧
     (∀ i k, EdgeChecks c i k ((c.core i).edges k)) ∧
     c.triangleAvoidance = decide (∀ i, TriangleDecision.checkAllTrianglesMA (c.node i) = true) ∧
     (c.triangleAvoidance = true → ∀ i, allTriangleDescentsCheck (c.node i) = true))
    ⟨fun ⟨a,b,d,e,f,g,h,j,k⟩ => ⟨a,
       (wordEntriesCheck_iff _ _ _ _).mp b,d,
       fun i => (wordEntriesCheck_iff _ _ _ _).mp (e i),f,g,h,j,k⟩,
     fun h => ⟨h.connected,
       (wordEntriesCheck_iff _ _ _ _).mpr h.entry,h.originWord,
       fun i => (wordEntriesCheck_iff _ _ _ _).mpr (h.reachable i),
       h.cyclic,h.strips,h.edges,h.triangles,h.descents⟩⟩

def accept (c : Certificate) : Bool := decide (Checks c)

theorem accept_iff (c : Certificate) : accept c = true ↔ Checks c := by
  simp only [accept,decide_eq_true_eq]

theorem edge_safe (c : Certificate) (hstrip : ∀ s, StripChecks c (c.strips s))
    (i : Fin (c.size+1)) (k : Fin 4) (e : EdgeRecord c.size c.stripCount)
    (h : EdgeChecks c i k e) : Safe c (mutate (c.node i) k) := by
  cases e with
  | core j f =>
    apply f.safe_inverse c
    rw [entriesEqual_eq h]
    exact safe_node c j
  | mstrip s n phase f =>
    apply f.safe_inverse c
    rw [entriesEqual_eq h.2]
    exact strip_safe c (c.strips s) (hstrip s) phase
  | boundary b =>
    have hb := boundaryChecks_sound b h.2.2.2
    rw [entriesEqual_eq h.2.1,h.1] at hb
    rcases hb with hf | hr
    · exact RecursiveRegions.Safe.fork k (safe_node c i) hf
    · exact RecursiveRegions.attach_root regionData (Base c) (safe_node c i) k hr
  | zero x u v w r => exact zero_entry_safe c _ (safe_node c i) k x u v w r h.1 h.2
  | pendant d x y r => exact pendant_entry_safe c _ (safe_node c i) k d x y r h.1 h.2

theorem checked_edges (c : Certificate) (h : Checks c)
    (B : Matrix 4) (hB : Base c B) (k : Fin 4) : Safe c (mutate B k) := by
  obtain ⟨i,rfl⟩ := hB
  exact edge_safe c h.strips i k _ (h.edges i k)

theorem checked_cyclic (c : Certificate) (h : Checks c)
    (B : Matrix 4) (hB : Base c B) : ¬ Acyclic B := by
  obtain ⟨i,rfl⟩ := hB
  exact fun ha => h.cyclic i ((ForkPruning.finiteAcyclic_iff _ (c.core i).quiver.skew).mpr ha)

theorem checked_NMA (c : Certificate) (h : Checks c) : ¬ MutationAcyclic c.initial.matrix := by
  apply CertificateTransport.entry_NMA c.initial.matrix (c.node 0) c.initial.skew
    c.entryWord c.entryFrame.relabeling c.entryFrame.flip (entriesEqual_eq h.entry)
  exact RecursiveRegions.safe_NMA regionData regionRules (Base c)
    (fun _ hB => base_skew c hB) (checked_cyclic c h) (checked_edges c h) (safe_node c 0)

theorem accept_NMA (c : Certificate) (h : accept c = true) : ¬ MutationAcyclic c.initial.matrix :=
  checked_NMA c ((accept_iff c).mp h)

theorem checked_triangles (c : Certificate) (h : Checks c) (hav : c.triangleAvoidance = true)
    (B : Matrix 4) (hB : Base c B) : AllTrianglesMA B := by
  obtain ⟨i,rfl⟩ := hB
  have ha : (∀ j, TriangleDecision.checkAllTrianglesMA (c.node j) = true) := by
    have hh := h.triangles
    rw [hav] at hh
    exact of_decide_eq_true hh.symm
  exact TriangleDecision.checkAllTrianglesMA_sound _ (c.core i).quiver.skew (ha i)

theorem checked_global_triangles (c : Certificate) (h : Checks c)
    (hav : c.triangleAvoidance = true) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord c.initial.matrix word) := by
  apply CertificateTransport.entry_global_triangles c.initial.matrix (c.node 0) c.initial.skew
    c.entryWord c.entryFrame.relabeling c.entryFrame.flip (entriesEqual_eq h.entry) _ word
  intro w
  exact RecursiveRegions.safe_global_triangle_avoidance regionData regionRules triangleRules
    (Base c) (fun _ hB => base_skew c hB) (checked_triangles c h hav) (checked_edges c h)
    (safe_node c 0) w

theorem accept_global_triangles (c : Certificate) (h : accept c = true)
    (hav : c.triangleAvoidance = true) (word : List (Fin 4)) :
    AllTrianglesMA (applyWord c.initial.matrix word) :=
  checked_global_triangles c ((accept_iff c).mp h) hav word

theorem checked_strip_reached (c : Certificate) (h : Checks c) (s : Fin c.stripCount) :
    (c.strips s).rootFrame.apply
      (applyWord (c.entryFrame.apply (applyWord c.initial.matrix c.entryWord)) (c.strips s).rootWord) =
      GenericStrip.root (c.strips s).m (c.strips s).a (c.strips s).b (c.strips s).c := by
  rw [entriesEqual_eq h.entry,entriesEqual_eq (h.strips s).2.2.1]
  exact entriesEqual_eq (h.strips s).2.2.2.1

theorem accept_no_L0 (c : Certificate) (h : accept c = true) (s : Fin c.stripCount)
    (cert : RegionCertificate) : acceptCertificate c.initial.matrix cert ≠ true := by
  have hc := (accept_iff c).mp h
  exact CertificateTransport.reachable_strip_no_L0 c.initial.matrix c.entryWord (c.strips s).rootWord
    c.entryFrame.relabeling (c.strips s).rootFrame.relabeling c.entryFrame.flip (c.strips s).rootFrame.flip
    (c.strips s).m (c.strips s).a (c.strips s).b (c.strips s).c (hc.strips s).1
    (checked_strip_reached c hc s) cert

end QuiverProofs.LStar
