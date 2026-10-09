import QuiverProofs.TriangleDecision

/-! A total counterpart of the verifier's constructive triangle loop.
Every recursive call is admitted only after checking strict decrease of the
sum of positive weights. Failure of that check returns rejection. -/
namespace QuiverProofs.LStar

structure WeightTriple where
  x : Nat
  y : Nat
  z : Nat

def WeightTriple.total (t : WeightTriple) : Nat := t.x+t.y+t.z

def sortWeights (t : WeightTriple) : WeightTriple :=
  if t.x ≤ t.y then
    if t.y ≤ t.z then t else if t.x ≤ t.z then ⟨t.x,t.z,t.y⟩ else ⟨t.z,t.x,t.y⟩
  else if t.x ≤ t.z then ⟨t.y,t.x,t.z⟩ else if t.y ≤ t.z then ⟨t.y,t.z,t.x⟩ else ⟨t.z,t.y,t.x⟩

theorem sortWeights_total (t : WeightTriple) : (sortWeights t).total = t.total := by
  unfold sortWeights WeightTriple.total
  split <;> split <;> (try split) <;> simp_all <;> omega

theorem sortWeights_sorted (t : WeightTriple) :
    (sortWeights t).x ≤ (sortWeights t).y ∧ (sortWeights t).y ≤ (sortWeights t).z := by
  unfold sortWeights
  split <;> split <;> (try split) <;> simp_all <;> omega

/-- The emitted list contains precisely the sorted triples encountered.
`none` is the verifier's decreasing-descent rejection. -/
def constructiveDescent (t : WeightTriple) : Option (List WeightTriple) :=
  let s := sortWeights t
  if s.x*s.y ≤ s.z then some [s]
  else if h : s.x*s.y-s.z < s.z then
    (constructiveDescent ⟨s.x,s.y,s.x*s.y-s.z⟩).map (s :: ·)
  else none
termination_by t.total
decreasing_by
  have hs := sortWeights_total t
  change (sortWeights t).x+(sortWeights t).y+((sortWeights t).x*(sortWeights t).y-(sortWeights t).z) < t.total
  have hh : (sortWeights t).x*(sortWeights t).y-(sortWeights t).z < (sortWeights t).z := h
  change (sortWeights t).x+(sortWeights t).y+(sortWeights t).z = t.x+t.y+t.z at hs
  change (sortWeights t).x+(sortWeights t).y+((sortWeights t).x*(sortWeights t).y-(sortWeights t).z) < t.x+t.y+t.z
  omega

instance (x y z : Int) : Decidable (TriangleDecision.CyclicSigns x y z) := by
  unfold TriangleDecision.CyclicSigns; infer_instance

def triangleDescentCheck (T : Matrix 3) : Bool :=
  if TriangleDecision.CyclicSigns (T 0 1) (T 1 2) (T 2 0) then
    (constructiveDescent ⟨(T 0 1).natAbs,(T 1 2).natAbs,(T 2 0).natAbs⟩).isSome
  else true

def allTriangleDescentsCheck (Q : Matrix 4) : Bool :=
  decide (∀ r : Fin 4,
    triangleDescentCheck (TriangleRegions.restrict Q (TriangleRegions.deleteVertex r)) = true)

end QuiverProofs.LStar
