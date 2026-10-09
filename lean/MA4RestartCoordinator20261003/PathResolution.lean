import MA4RestartCoordinator20261003.FreePathProjectives
import MA4RestartCoordinator20261003.VertexRestriction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Actual arrow-relation maps for the fixed representation model. All arrow
multiplicities are those of the original integer matrix. No finite path set,
hereditary premise, or supplied exact resolution is introduced. -/
namespace QuiverProofs.MA4RestartPathResolution
open CategoryTheory CategoryTheory.Limits
open QuiverProofs.MA4RestartWeightedQuiverModel
open QuiverProofs.MA4RestartFreePathProjectives
open QuiverProofs.MA4RestartVertexRestriction
set_option maxHeartbeats 0
noncomputable section
variable (B : Matrix 4) (K : Type) [Field K]

local instance representationFiniteBiproducts : HasFiniteBiproducts (Representation B K) :=
  Abelian.hasFiniteBiproducts

abbrev Arrow := Σ i : Vertex B, Σ j : Vertex B, Quiver.Hom i j

instance arrowFintype : Fintype (Arrow B) := by unfold Arrow; infer_instance

def coverInclusion (M : Representation B K) (i : Vertex B) :
    freePath B K i (M.obj i) ⟶ freeCover B K M :=
  biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) i

def freeRelations (M : Representation B K) : Representation B K :=
  ⨁ fun a : Arrow B => freePath B K a.2.1 (M.obj a.1)

def relationInclusion (M : Representation B K) (a : Arrow B) :
    freePath B K a.2.1 (M.obj a.1) ⟶ freeRelations B K M :=
  biproduct.ι (fun b : Arrow B => freePath B K b.2.1 (M.obj b.1)) a

theorem freeRelations_projective (M : Representation B K) :
    Projective (freeRelations B K M) := by
  letI (a : Arrow B) : Projective (freePath B K a.2.1 (M.obj a.1)) :=
    freePath_projective B K a.2.1 (M.obj a.1)
  unfold freeRelations
  infer_instance

theorem freeCoverTo_generator (M : Representation B K) (i j : Paths (Vertex B))
    (p : i ⟶ j) (x : M.obj i) :
    (freeCoverTo B K M).app j
      ((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) i).app j
        (Finsupp.single p x)) = M.map p x := by
  change ((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) i ≫
    freeCoverTo B K M).app j) (Finsupp.single p x) = M.map p x
  rw [freeCoverTo, biproduct.ι_desc, freePathDesc_single]
  simp

/-- The defining relation transports a vector along an arrow in the two ways. -/
def relationGenerator (M : Representation B K) (a : Arrow B) :
    M.obj a.1 ⟶ (freeCover B K M).obj a.2.1 :=
  ModuleCat.ofHom
    (((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) a.1).app a.2.1).hom.comp
        (Finsupp.lsingle a.2.2.toPath) -
      ((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) a.2.1).app a.2.1).hom.comp
        ((Finsupp.lsingle (Quiver.Path.nil : Quiver.Path a.2.1 a.2.1)).comp
          (M.map a.2.2.toPath).hom))

def relationMap (M : Representation B K) : freeRelations B K M ⟶ freeCover B K M :=
  biproduct.desc fun a =>
    freePathDesc B K a.2.1 (M.obj a.1) (freeCover B K M) (relationGenerator B K M a)

theorem relationGenerator_augmentation (M : Representation B K) (a : Arrow B) :
    relationGenerator B K M a ≫ (freeCoverTo B K M).app a.2.1 = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change (freeCoverTo B K M).app a.2.1
    (((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) a.1).app a.2.1)
        (Finsupp.single a.2.2.toPath x) -
      ((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) a.2.1).app a.2.1)
        (Finsupp.single (Quiver.Path.nil : Quiver.Path a.2.1 a.2.1)
          (M.map a.2.2.toPath x))) = 0
  rw [map_sub, freeCoverTo_generator, freeCoverTo_generator]
  have hn : M.map (Quiver.Path.nil : Quiver.Path a.2.1 a.2.1) = 𝟙 (M.obj a.2.1) :=
    M.map_id (a.2.1 : Paths (Vertex B))
  rw [hn]
  simp

/-- The actual natural maps compose to zero, with no next-state assumptions. -/
theorem relationMap_augmentation (M : Representation B K) :
    relationMap B K M ≫ freeCoverTo B K M = 0 := by
  apply biproduct.hom_ext'
  intro a
  rw [← Category.assoc, relationMap, biproduct.ι_desc]
  apply (freePathHomEquiv B K a.2.1 (M.obj a.1) M).injective
  change freePathRestrict B K a.2.1 (M.obj a.1) M
    (freePathDesc B K a.2.1 (M.obj a.1) (freeCover B K M) (relationGenerator B K M a) ≫
      freeCoverTo B K M) = freePathRestrict B K a.2.1 (M.obj a.1) M 0
  rw [freePathRestrict_comp, freePathRestrict_desc, relationGenerator_augmentation]
  apply ModuleCat.hom_ext
  rfl

def resolutionComplex (M : Representation B K) : ShortComplex (Representation B K) :=
  ShortComplex.mk (relationMap B K M) (freeCoverTo B K M) (relationMap_augmentation B K M)

/-- A pointwise nil-path section. It is not asserted to be natural. -/
def nilSection (M : Representation B K) (j : Paths (Vertex B)) :
    M.obj j ⟶ (freeCover B K M).obj j :=
  ModuleCat.ofHom
    (((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) j).app j).hom.comp
      (Finsupp.lsingle (𝟙 j)))

theorem nilSection_augmentation (M : Representation B K) (j : Paths (Vertex B)) :
    nilSection B K M j ≫ (freeCoverTo B K M).app j = 𝟙 (M.obj j) := by
  apply ModuleCat.hom_ext
  ext x
  change (freeCoverTo B K M).app j
    (((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) j).app j)
      (Finsupp.single (𝟙 j) x)) = x
  rw [freeCoverTo_generator]
  simp

/-- The pointwise chain homotopy is defined by induction on the actual finite
path. Its values lie in a finite-support arrow sum even when paths are infinite. -/
def pathChain (M : Representation B K) (i : Vertex B) {j : Vertex B}
    (p : Quiver.Path i j) : M.obj i →ₗ[K] (freeRelations B K M).obj j :=
  @Quiver.Path.rec (Vertex B) (weightedQuiver B) i
    (fun l _ => M.obj i →ₗ[K] (freeRelations B K M).obj l) 0
    (fun {b c} q e ih =>
      ((freeRelations B K M).map e.toPath).hom.comp ih +
        ((relationInclusion B K M ⟨b, ⟨c, e⟩⟩).app c).hom.comp
          ((Finsupp.lsingle (Quiver.Path.nil : Quiver.Path c c)).comp (M.map q).hom)) j p

theorem pathChain_nil (M : Representation B K) (i : Vertex B) :
    pathChain B K M i (Quiver.Path.nil : Quiver.Path i i) = 0 := rfl

theorem pathChain_cons (M : Representation B K) {i b j : Vertex B}
    (p : Quiver.Path i b) (e : Quiver.Hom b j) :
    pathChain B K M i (p.cons e) =
      ((freeRelations B K M).map e.toPath).hom.comp (pathChain B K M i p) +
        ((relationInclusion B K M ⟨b, ⟨j, e⟩⟩).app j).hom.comp
          ((Finsupp.lsingle (Quiver.Path.nil : Quiver.Path j j)).comp (M.map p).hom) := rfl

theorem relationMap_nil (M : Representation B K) (a : Arrow B) (x : M.obj a.1) :
    (relationMap B K M).app a.2.1
      (((biproduct.ι (fun b : Arrow B => freePath B K b.2.1 (M.obj b.1)) a).app a.2.1)
        (Finsupp.single (Quiver.Path.nil : Quiver.Path a.2.1 a.2.1) x)) =
      relationGenerator B K M a x := by
  change ((biproduct.ι (fun b : Arrow B => freePath B K b.2.1 (M.obj b.1)) a ≫
    relationMap B K M).app a.2.1)
      (Finsupp.single (Quiver.Path.nil : Quiver.Path a.2.1 a.2.1) x) = _
  rw [relationMap, biproduct.ι_desc, freePathDesc_single]
  have hn : (freeCover B K M).map (Quiver.Path.nil : Quiver.Path a.2.1 a.2.1) =
      𝟙 ((freeCover B K M).obj a.2.1) := (freeCover B K M).map_id _
  rw [hn]
  simp

theorem cover_transport_generator (M : Representation B K)
    (i j l : Paths (Vertex B)) (p : i ⟶ j) (g : j ⟶ l) (x : M.obj i) :
    (freeCover B K M).map g
      (((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) i).app j)
        (Finsupp.single p x)) =
      ((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) i).app l)
        (Finsupp.single (p ≫ g) x) := by
  have h := congrArg (fun f : (freePath B K i (M.obj i)).obj j ⟶
      (freeCover B K M).obj l => f (Finsupp.single p x))
    ((biproduct.ι (fun v : Vertex B => freePath B K v (M.obj v)) i).naturality g)
  simpa [freePath] using h.symm

/-- The pointwise chain boundary telescopes along a path to its endpoints. -/
theorem pathChain_boundary (M : Representation B K) (i : Vertex B)
    {j : Vertex B} (p : Quiver.Path i j) (x : M.obj i) :
    (relationMap B K M).app j (pathChain B K M i p x) =
      (coverInclusion B K M i).app j
        (Finsupp.single p x) - nilSection B K M j (M.map p x) := by
  induction p with
  | nil =>
      have hn : M.map (Quiver.Path.nil : Quiver.Path i i) = 𝟙 (M.obj i) := M.map_id _
      simp only [pathChain_nil, LinearMap.zero_apply, map_zero]
      rw [hn]
      change 0 = (coverInclusion B K M i).app i (Finsupp.single Quiver.Path.nil x) -
        (coverInclusion B K M i).app i (Finsupp.single Quiver.Path.nil x)
      simp
  | @cons b j p e ih =>
      simp only [pathChain_cons, LinearMap.add_apply, LinearMap.comp_apply, map_add]
      have hn := congrArg (fun f : (freeRelations B K M).obj b ⟶
          (freeCover B K M).obj j => f (pathChain B K M i p x))
        ((relationMap B K M).naturality e.toPath)
      rw [show (relationMap B K M).app j
          ((freeRelations B K M).map e.toPath (pathChain B K M i p x)) =
          (freeCover B K M).map e.toPath
            ((relationMap B K M).app b (pathChain B K M i p x)) from hn]
      rw [ih, map_sub]
      change (freeCover B K M).map e.toPath
          (((coverInclusion B K M i).app b)
            (Finsupp.single p x)) -
        (freeCover B K M).map e.toPath
          (((coverInclusion B K M b).app b)
            (Finsupp.single Quiver.Path.nil (M.map p x))) +
        (relationMap B K M).app j
          (((relationInclusion B K M ⟨b, ⟨j, e⟩⟩).app j)
            (Finsupp.single Quiver.Path.nil (M.map p x))) = _
      simp only [coverInclusion, relationInclusion]
      erw [cover_transport_generator B K M i b j p e.toPath x,
        cover_transport_generator B K M b b j Quiver.Path.nil e.toPath (M.map p x),
        relationMap_nil B K M ⟨b, ⟨j, e⟩⟩ (M.map p x)]
      have hm : M.map (p.cons e) = M.map p ≫ M.map e.toPath := M.map_comp p e.toPath
      erw [hm]
      change (coverInclusion B K M i).app j (Finsupp.single (p.cons e) x) -
          (coverInclusion B K M b).app j (Finsupp.single e.toPath (M.map p x)) +
        ((coverInclusion B K M b).app j (Finsupp.single e.toPath (M.map p x)) -
          (coverInclusion B K M j).app j
            (Finsupp.single Quiver.Path.nil (M.map e.toPath (M.map p x)))) =
        (coverInclusion B K M i).app j (Finsupp.single (p.cons e) x) -
          (coverInclusion B K M j).app j
            (Finsupp.single Quiver.Path.nil (M.map e.toPath (M.map p x)))
      abel

theorem relation_transport_generator (M : Representation B K) (a : Arrow B)
    (j l : Vertex B) (p : Quiver.Path a.2.1 j) (g : Quiver.Path j l)
    (x : M.obj a.1) :
    (freeRelations B K M).map g
      ((relationInclusion B K M a).app j (Finsupp.single p x)) =
      (relationInclusion B K M a).app l (Finsupp.single (p.comp g) x) := by
  have h := congrArg (fun f : (freePath B K a.2.1 (M.obj a.1)).obj j ⟶
      (freeRelations B K M).obj l => f (Finsupp.single p x))
    ((relationInclusion B K M a).naturality g)
  simpa [freePath] using h.symm

/-- Peeling the first arrow gives the cancellation needed for a left inverse
of the relation differential. -/
theorem pathChain_first_edge (M : Representation B K) {i k j : Vertex B}
    (e : Quiver.Hom i k) (p : Quiver.Path k j) (x : M.obj i) :
    pathChain B K M i (e.toPath.comp p) x =
      (relationInclusion B K M ⟨i, ⟨k, e⟩⟩).app j (Finsupp.single p x) +
        pathChain B K M k p (M.map e.toPath x) := by
  induction p with
  | nil =>
      have hn : M.map (Quiver.Path.nil : Quiver.Path i i) = 𝟙 (M.obj i) := M.map_id _
      simp only [Quiver.Path.comp_nil, Quiver.Hom.toPath, pathChain_nil, pathChain_cons,
        LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_zero]
      rw [hn]
      change 0 + (relationInclusion B K M ⟨i, ⟨k, e⟩⟩).app k (Finsupp.single Quiver.Path.nil x) =
        (relationInclusion B K M ⟨i, ⟨k, e⟩⟩).app k (Finsupp.single Quiver.Path.nil x) + 0
      simp
  | @cons b j p f ih =>
      simp only [Quiver.Path.comp_cons, pathChain_cons, LinearMap.add_apply,
        LinearMap.comp_apply, ih, map_add]
      erw [relation_transport_generator B K M ⟨i, ⟨k, e⟩⟩ b j p f.toPath x]
      have hm : M.map (e.toPath.comp p) = M.map e.toPath ≫ M.map p :=
        M.map_comp e.toPath p
      erw [hm]
      change (relationInclusion B K M ⟨i, ⟨k, e⟩⟩).app j (Finsupp.single (p.cons f) x) +
          (freeRelations B K M).map f.toPath (pathChain B K M k p (M.map e.toPath x)) +
          (relationInclusion B K M ⟨b, ⟨j, f⟩⟩).app j
            (Finsupp.single Quiver.Path.nil (M.map p (M.map e.toPath x))) =
        (relationInclusion B K M ⟨i, ⟨k, e⟩⟩).app j (Finsupp.single (p.cons f) x) +
          ((freeRelations B K M).map f.toPath (pathChain B K M k p (M.map e.toPath x)) +
            (relationInclusion B K M ⟨b, ⟨j, f⟩⟩).app j
              (Finsupp.single Quiver.Path.nil (M.map p (M.map e.toPath x))))
      abel

/-- Only a linear map at a vertex: no naturality over arrows is asserted. -/
def coverHomotopy (M : Representation B K) (j : Paths (Vertex B)) :
    (freeCover B K M).obj j ⟶ (freeRelations B K M).obj j :=
  (((evaluation (Paths (Vertex B)) (ModuleCat.{0} K)).obj j).mapBiproduct
      (fun i : Vertex B => freePath B K i (M.obj i))).hom ≫
    biproduct.desc (fun i : Vertex B =>
      ModuleCat.ofHom (Finsupp.lsum K (fun p : Quiver.Path i j =>
        pathChain B K M i p)))

theorem coverHomotopy_generator (M : Representation B K)
    (i j : Paths (Vertex B)) (p : i ⟶ j) (x : M.obj i) :
    coverHomotopy B K M j ((coverInclusion B K M i).app j (Finsupp.single p x)) =
      pathChain B K M i p x := by
  let F := (evaluation (Paths (Vertex B)) (ModuleCat.{0} K)).obj j
  let T := fun v : Vertex B => freePath B K v (M.obj v)
  have hi : (coverInclusion B K M i).app j ≫ (F.mapBiproduct T).hom =
      biproduct.ι (F.obj ∘ T) i := by
    apply (cancel_mono (F.mapBiproduct T).inv).mp
    rw [Category.assoc]
    erw [Iso.hom_inv_id, Category.comp_id, Functor.mapBiproduct_inv, biproduct.ι_desc]
    rfl
  change (((coverInclusion B K M i).app j ≫ coverHomotopy B K M j))
    (Finsupp.single p x) = _
  rw [coverHomotopy, ← Category.assoc, hi, biproduct.ι_desc]
  exact Finsupp.lsum_single K _ p x

theorem vertex_biproduct_hom_ext {I : Type} [Finite I] (T : I → Representation B K)
    (j : Paths (Vertex B)) {X : ModuleCat.{0} K} {f g : (⨁ T).obj j ⟶ X}
    (h : ∀ i, (biproduct.ι T i).app j ≫ f = (biproduct.ι T i).app j ≫ g) : f = g := by
  let F := (evaluation (Paths (Vertex B)) (ModuleCat.{0} K)).obj j
  apply (cancel_epi (F.mapBiproduct T).inv).mp
  apply biproduct.hom_ext'
  intro i
  erw [← Category.assoc, Functor.mapBiproduct_inv, biproduct.ι_desc]
  erw [← Category.assoc, biproduct.ι_desc]
  exact h i

theorem relationMap_generator (M : Representation B K) (a : Arrow B)
    (j : Vertex B) (p : Quiver.Path a.2.1 j) (x : M.obj a.1) :
    (relationMap B K M).app j
      ((relationInclusion B K M a).app j (Finsupp.single p x)) =
      (coverInclusion B K M a.1).app j (Finsupp.single (a.2.2.toPath.comp p) x) -
        (coverInclusion B K M a.2.1).app j
          (Finsupp.single p (M.map a.2.2.toPath x)) := by
  change ((relationInclusion B K M a ≫ relationMap B K M).app j)
    (Finsupp.single p x) = _
  rw [relationInclusion, relationMap, biproduct.ι_desc, freePathDesc_single]
  change (freeCover B K M).map p
    ((coverInclusion B K M a.1).app a.2.1 (Finsupp.single a.2.2.toPath x) -
      (coverInclusion B K M a.2.1).app a.2.1
        (Finsupp.single Quiver.Path.nil (M.map a.2.2.toPath x))) = _
  rw [map_sub]
  simp only [coverInclusion]
  erw [cover_transport_generator B K M a.1 a.2.1 j a.2.2.toPath p x,
    cover_transport_generator B K M a.2.1 a.2.1 j Quiver.Path.nil p (M.map a.2.2.toPath x)]
  change (coverInclusion B K M a.1).app j (Finsupp.single (a.2.2.toPath.comp p) x) -
      (coverInclusion B K M a.2.1).app j
        (Finsupp.single (Quiver.Path.nil.comp p) (M.map a.2.2.toPath x)) = _
  rw [Quiver.Path.nil_comp]
  rfl

/-- The homotopy is a genuine left inverse of the relation map at each vertex. -/
theorem relationMap_coverHomotopy (M : Representation B K) (j : Vertex B) :
    (relationMap B K M).app j ≫ coverHomotopy B K M j =
      𝟙 ((freeRelations B K M).obj j) := by
  apply vertex_biproduct_hom_ext B K (fun a : Arrow B => freePath B K a.2.1 (M.obj a.1)) j
  intro a
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro p x
  change coverHomotopy B K M j
    ((relationMap B K M).app j
      ((relationInclusion B K M a).app j (Finsupp.single p x))) =
    (relationInclusion B K M a).app j (Finsupp.single p x)
  rw [relationMap_generator, map_sub]
  erw [coverHomotopy_generator B K M a.1 j (a.2.2.toPath.comp p) x,
    coverHomotopy_generator B K M a.2.1 j p (M.map a.2.2.toPath x),
    pathChain_first_edge B K M a.2.2 p x]
  abel

/-- The other homotopy identity supplies pointwise exactness, without a
globally natural section or retraction in the path representation category. -/
theorem coverHomotopy_boundary (M : Representation B K) (j : Vertex B) :
    coverHomotopy B K M j ≫ (relationMap B K M).app j +
      (freeCoverTo B K M).app j ≫ nilSection B K M j =
        𝟙 ((freeCover B K M).obj j) := by
  apply vertex_biproduct_hom_ext B K (fun i : Vertex B => freePath B K i (M.obj i)) j
  intro i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro p x
  change (relationMap B K M).app j
      (coverHomotopy B K M j ((coverInclusion B K M i).app j (Finsupp.single p x))) +
    nilSection B K M j
      ((freeCoverTo B K M).app j ((coverInclusion B K M i).app j (Finsupp.single p x))) =
    (coverInclusion B K M i).app j (Finsupp.single p x)
  erw [coverHomotopy_generator B K M i j p x,
    freeCoverTo_generator B K M i j p x, pathChain_boundary B K M i p x]
  abel

/-- Pointwise maps are natural over the discrete vertex family. -/
def discreteResolutionSplitting (M : Representation B K) :
    ((resolutionComplex B K M).map (vertexRestriction B K)).Splitting where
  r := Discrete.natTrans (fun j => coverHomotopy B K M j.as)
  s := Discrete.natTrans (fun j => nilSection B K M j.as)
  f_r := by
    apply NatTrans.ext
    funext j
    exact relationMap_coverHomotopy B K M j.as
  s_g := by
    apply NatTrans.ext
    funext j
    exact nilSection_augmentation B K M j.as
  id := by
    apply NatTrans.ext
    funext j
    exact coverHomotopy_boundary B K M j.as

theorem resolution_exact (M : Representation B K) : (resolutionComplex B K M).Exact :=
  (restriction_exact_iff B K (resolutionComplex B K M)).mp
    (discreteResolutionSplitting B K M).exact

theorem relationMap_mono (M : Representation B K) : Mono (relationMap B K M) :=
  (vertexRestriction B K).mono_of_mono_map
    (show Mono ((vertexRestriction B K).map (relationMap B K M)) from
      (discreteResolutionSplitting B K M).mono_f)

/-- The actual arrow-relation and vertex-cover maps form a projective
length-one short exact sequence for every representation in the fixed model. -/
theorem resolution_shortExact (M : Representation B K) :
    (resolutionComplex B K M).ShortExact :=
  ShortComplex.ShortExact.mk' (resolution_exact B K M)
    (relationMap_mono B K M) (freeCoverTo_epi B K M)

#print axioms resolution_exact
#print axioms relationMap_mono
#print axioms resolution_shortExact

end
end QuiverProofs.MA4RestartPathResolution
