import QuiverProofs.Disconnected
import QuiverProofs.TriangleRegions

/-! An exact computable version of the source triangle-status test.
The three signed coordinates may be arbitrary integers. The only finite
enumeration used by the imported classification is of orientation signs;
there is no bound on weights or mutation words. -/
namespace QuiverProofs.TriangleDecision

/-- The two cyclic orientations of the signed edges 01,12,20. -/
def CyclicSigns (x y z : Int) : Prop :=
  (0<x ∧ 0<y ∧ 0<z) ∨ (x<0 ∧ y<0 ∧ z<0)

/-- Exactly the Python NMA-triangle condition, with integer absolute values. -/
def triNMACondition (x y z : Int) : Prop :=
  CyclicSigns x y z ∧
  (2 : Int) ≤ min (x.natAbs : Int) (min (y.natAbs : Int) (z.natAbs : Int)) ∧
  triangleMarkov (x.natAbs : Int) (y.natAbs : Int) (z.natAbs : Int) ≤ 4

instance (x y z : Int) : Decidable (triNMACondition x y z) := by
  unfold triNMACondition CyclicSigns
  infer_instance

theorem triNMACondition_iff_signed (x y z : Int) :
    triNMACondition x y z ↔ SignedTriangleRegion x y z := by
  constructor
  · rintro ⟨hc,hmin,hC⟩
    have hx : (2 : Int) ≤ (x.natAbs : Int) := by omega
    have hy : (2 : Int) ≤ (y.natAbs : Int) := by omega
    have hz : (2 : Int) ≤ (z.natAbs : Int) := by omega
    rcases hc with hp|hn
    · have ax := Int.natAbs_of_nonneg (show 0≤x by omega)
      have ay := Int.natAbs_of_nonneg (show 0≤y by omega)
      have az := Int.natAbs_of_nonneg (show 0≤z by omega)
      rw [ax,ay,az] at hC
      exact Or.inl ⟨by omega,by omega,by omega,hC⟩
    · have ax := Int.ofNat_natAbs_of_nonpos (show x≤0 by omega)
      have ay := Int.ofNat_natAbs_of_nonpos (show y≤0 by omega)
      have az := Int.ofNat_natAbs_of_nonpos (show z≤0 by omega)
      rw [ax,ay,az] at hC
      exact Or.inr ⟨by omega,by omega,by omega,hC⟩
  · intro h
    rcases h with ⟨hx,hy,hz,hC⟩|⟨hx,hy,hz,hC⟩
    · have ax := Int.natAbs_of_nonneg (show 0≤x by omega)
      have ay := Int.natAbs_of_nonneg (show 0≤y by omega)
      have az := Int.natAbs_of_nonneg (show 0≤z by omega)
      refine ⟨Or.inl ⟨by omega,by omega,by omega⟩,?_,?_⟩
      · omega
      · simpa only [ax,ay,az] using hC
    · have ax := Int.ofNat_natAbs_of_nonpos (show x≤0 by omega)
      have ay := Int.ofNat_natAbs_of_nonpos (show y≤0 by omega)
      have az := Int.ofNat_natAbs_of_nonpos (show z≤0 by omega)
      refine ⟨Or.inr ⟨by omega,by omega,by omega⟩,?_,?_⟩
      · omega
      · simpa only [ax,ay,az] using hC

/-- Skew symmetry determines every entry from the three cyclic coordinates. -/
theorem skew_eq_cycleThree (T : Matrix 3) (hT : SkewSymmetric T) :
    T = cycleThree (T 0 1) (T 1 2) (T 2 0) := by
  have h00 := hT 0 0
  have h11 := hT 1 1
  have h22 := hT 2 2
  have h10 := hT 1 0
  have h21 := hT 2 1
  have h02 := hT 0 2
  funext i j
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  have hj : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
    simp only [cycleThree] <;> omega

theorem triNMACondition_iff_NMA (T : Matrix 3) (hT : SkewSymmetric T) :
    triNMACondition (T 0 1) (T 1 2) (T 2 0) ↔ ¬ MutationAcyclic T := by
  rw [triNMACondition_iff_signed,←signed_triangle_NMA_iff]
  exact iff_of_eq (congrArg (fun B => ¬MutationAcyclic B) (skew_eq_cycleThree T hT).symm)

/-- True exactly when the source criterion says that this triangle is MA. -/
def checkTriMA (T : Matrix 3) : Bool :=
  decide (¬triNMACondition (T 0 1) (T 1 2) (T 2 0))

theorem checkTriMA_iff (T : Matrix 3) (hT : SkewSymmetric T) :
    checkTriMA T = true ↔ MutationAcyclic T := by
  simp only [checkTriMA,decide_eq_true_eq,triNMACondition_iff_NMA T hT]
  exact ⟨Classical.byContradiction,fun h hn => hn h⟩

theorem checkTriMA_sound (T : Matrix 3) (hT : SkewSymmetric T)
    (hcheck : checkTriMA T = true) : MutationAcyclic T :=
  (checkTriMA_iff T hT).mp hcheck

theorem checkTriMA_false_iff (T : Matrix 3) (hT : SkewSymmetric T) :
    checkTriMA T = false ↔ ¬ MutationAcyclic T := by
  rw [←checkTriMA_iff T hT]
  cases checkTriMA T <;> simp

/-- The four sorted vertex-deletion triangles, exactly as in the source check. -/
def checkAllTrianglesMA (Q : Matrix 4) : Bool :=
  decide (∀ r : Fin 4,
    checkTriMA (TriangleRegions.restrict Q (TriangleRegions.deleteVertex r)) = true)

theorem checkAllTrianglesMA_iff (Q : Matrix 4) (hQ : SkewSymmetric Q) :
    checkAllTrianglesMA Q = true ↔ TriangleRegions.AllTrianglesMA Q := by
  simp only [checkAllTrianglesMA,decide_eq_true_eq]
  rw [TriangleRegions.allTrianglesMA_iff_deletions]
  constructor
  · intro h r
    exact (checkTriMA_iff _ (TriangleRegions.restrict_skew Q _ hQ)).mp (h r)
  · intro h r
    exact (checkTriMA_iff _ (TriangleRegions.restrict_skew Q _ hQ)).mpr (h r)

theorem checkAllTrianglesMA_sound (Q : Matrix 4) (hQ : SkewSymmetric Q)
    (hcheck : checkAllTrianglesMA Q = true) : TriangleRegions.AllTrianglesMA Q :=
  (checkAllTrianglesMA_iff Q hQ).mp hcheck

theorem checkAllTrianglesMA_false_iff (Q : Matrix 4) (hQ : SkewSymmetric Q) :
    checkAllTrianglesMA Q = false ↔ ¬TriangleRegions.AllTrianglesMA Q := by
  rw [←checkAllTrianglesMA_iff Q hQ]
  cases checkAllTrianglesMA Q <;> simp

end QuiverProofs.TriangleDecision
