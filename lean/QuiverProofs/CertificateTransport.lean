import QuiverProofs.StripTriangles
import QuiverProofs.L0Exclusion
import QuiverProofs.ProperObstructionSoundness

/-! Exact mutation-word and signed-frame transport for certificate inputs.
The finite-cover statements are independent of NMA and triangle avoidance. -/
namespace QuiverProofs.CertificateTransport
open CertificateSearch ExtendedWeakPairs TriangleRegions

theorem transport_inverse (B : Matrix 4) (p : Relabeling 4) (flip : Bool) :
    transport (transport B p flip) p.symm flip = B := by
  cases flip <;> funext i j <;> simp [transport,relabel,reverse,Relabeling.symm,p.right_inv]

theorem transport_skew (B : Matrix 4) (p : Relabeling 4) (flip : Bool)
    (h : SkewSymmetric B) : SkewSymmetric (transport B p flip) := by
  cases flip
  · exact relabel_skew _ p h
  · exact relabel_skew _ p (reverse_skew _ h)

theorem transport_MA_iff (B : Matrix 4) (p : Relabeling 4) (flip : Bool)
    (h : SkewSymmetric B) : MutationAcyclic (transport B p flip) ↔ MutationAcyclic B := by
  cases flip
  · exact MA_relabel_iff B p
  · exact (MA_relabel_iff (reverse B) p).trans (MA_reverse_iff B h)

theorem cover_word {B : Matrix 4} (h : FiniteCoreExteriorCover B) (entry : List (Fin 4)) :
    FiniteCoreExteriorCover (applyWord B entry) := by
  obtain ⟨candidates,hc⟩ := h
  exact ⟨candidates,fun word => by simpa only [applyWord_append] using hc (entry ++ word)⟩

theorem cover_relabel {B : Matrix 4} (h : FiniteCoreExteriorCover B) (p : Relabeling 4) :
    FiniteCoreExteriorCover (relabel B p) := by
  obtain ⟨candidates,hc⟩ := h
  refine ⟨candidates,?_⟩
  intro word
  rw [word_relabel]
  rcases hc (word.map p.toFun) with ⟨C,hC,q,hq⟩ | he
  · exact Or.inl ⟨C,hC,q.trans p,by rw [hq]; rfl⟩
  · exact Or.inr (Exterior.framed he p)

theorem cover_reverse {B : Matrix 4} (h : FiniteCoreExteriorCover B) :
    FiniteCoreExteriorCover (reverse B) := by
  obtain ⟨candidates,hc⟩ := h
  refine ⟨candidates.map reverse,?_⟩
  intro word
  rw [word_reverse]
  rcases hc word with ⟨C,hC,p,hp⟩ | he
  · exact Or.inl ⟨reverse C,List.mem_map.mpr ⟨C,hC,rfl⟩,p,by rw [hp]; rfl⟩
  · exact Or.inr (Exterior.reversed he)

theorem cover_transport {B : Matrix 4} (h : FiniteCoreExteriorCover B)
    (p : Relabeling 4) (flip : Bool) : FiniteCoreExteriorCover (transport B p flip) := by
  cases flip
  · exact cover_relabel h p
  · exact cover_relabel (cover_reverse h) p

def GlobalTriangles (B : Matrix 4) : Prop :=
  ∀ word : List (Fin 4), AllTrianglesMA (applyWord B word)

theorem global_triangles_word {B : Matrix 4} (h : GlobalTriangles B)
    (entry : List (Fin 4)) : GlobalTriangles (applyWord B entry) := by
  intro word
  simpa only [applyWord_append] using h (entry ++ word)

theorem global_triangles_relabel {B : Matrix 4} (h : GlobalTriangles B)
    (p : Relabeling 4) : GlobalTriangles (relabel B p) := by
  intro word
  rw [word_relabel]
  exact triangles_relabel _ p (h (word.map p.toFun))

theorem global_triangles_reverse {B : Matrix 4} (hB : SkewSymmetric B)
    (h : GlobalTriangles B) : GlobalTriangles (reverse B) := by
  intro word
  rw [word_reverse]
  exact triangles_reverse _ (word_preserves_skew B word hB) (h word)

theorem global_triangles_transport {B : Matrix 4} (hB : SkewSymmetric B)
    (h : GlobalTriangles B) (p : Relabeling 4) (flip : Bool) :
    GlobalTriangles (transport B p flip) := by
  cases flip
  · exact global_triangles_relabel h p
  · exact global_triangles_relabel (global_triangles_reverse hB h) p

theorem entry_NMA (B C : Matrix 4) (hB : SkewSymmetric B)
    (entry : List (Fin 4)) (p : Relabeling 4) (flip : Bool)
    (heq : transport (applyWord B entry) p flip = C) (h : ¬ MutationAcyclic C) :
    ¬ MutationAcyclic B := by
  intro ha
  apply h
  rw [←heq]
  exact (transport_MA_iff _ p flip (word_preserves_skew B entry hB)).mpr
    ((mutationAcyclic_word_iff B entry).mpr ha)

theorem entry_global_triangles (B C : Matrix 4) (hB : SkewSymmetric B)
    (entry : List (Fin 4)) (p : Relabeling 4) (flip : Bool)
    (heq : transport (applyWord B entry) p flip = C) (h : GlobalTriangles C) :
    GlobalTriangles B := by
  have hC : SkewSymmetric C := by
    rw [←heq]; exact transport_skew _ p flip (word_preserves_skew B entry hB)
  have hb := global_triangles_transport hC h p.symm flip
  rw [←heq,transport_inverse] at hb
  have hout := global_triangles_word hb entry.reverse
  rwa [ProperObstructionSoundness.applyWord_undo] at hout

/-- A strip may be reached after a framed entry into the finite core and a
separate core reachability word. Both words are arbitrary finite lists. -/
theorem reachable_strip_no_finite_cover (B : Matrix 4)
    (entry rootWord : List (Fin 4)) (entryFrame rootFrame : Relabeling 4)
    (entryFlip rootFlip : Bool) (m a b c : Int) (hd : GenericStrip.Domain m a b c)
    (heq : transport (applyWord (transport (applyWord B entry) entryFrame entryFlip) rootWord)
      rootFrame rootFlip = GenericStrip.root m a b c) :
    ¬ FiniteCoreExteriorCover B := by
  intro h
  apply StripTriangles.no_finite_core_exterior_cover m a b c hd
  rw [←heq]
  exact cover_transport (cover_word (cover_transport (cover_word h entry)
    entryFrame entryFlip) rootWord) rootFrame rootFlip

theorem reachable_strip_no_L0 (B : Matrix 4)
    (entry rootWord : List (Fin 4)) (entryFrame rootFrame : Relabeling 4)
    (entryFlip rootFlip : Bool) (m a b c : Int) (hd : GenericStrip.Domain m a b c)
    (heq : transport (applyWord (transport (applyWord B entry) entryFrame entryFlip) rootWord)
      rootFrame rootFlip = GenericStrip.root m a b c)
    (cert : RegionCertificate) : acceptCertificate B cert ≠ true := by
  intro hc
  exact reachable_strip_no_finite_cover B entry rootWord entryFrame rootFrame entryFlip rootFlip
    m a b c hd heq (L0Exclusion.accepted_implies_finite_cover B cert hc)

end QuiverProofs.CertificateTransport
