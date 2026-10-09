import QuiverProofs.CensusData

/-! Data-only normalized syntax of `cyclic-core-mstrip-unit-pendant-v1`.
Finite index types encode validated list lengths, labels and record numbering.
No mathematical proof or additional witness is part of a record. This typed
syntax does not itself assert a correspondence with the external JSON parser. -/
namespace QuiverProofs.LStar

structure Six where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int

def Six.matrix (q : Six) : Matrix 4 := ofSix q.a q.b q.c q.d q.e q.f

theorem Six.skew (q : Six) : SkewSymmetric q.matrix := ofSix_skew _ _ _ _ _ _

structure Frame where
  permutation : Fin 24
  flip : Bool

def Frame.relabeling (f : Frame) : Relabeling 4 := Census.permutation f.permutation

def Frame.apply (f : Frame) (Q : Matrix 4) : Matrix 4 :=
  relabel (if f.flip then reverse Q else Q) f.relabeling

inductive BoundaryKind where
  | fork
  | diamond (s t : Fin 4)
  | unit (s t : Fin 4)

structure BoundaryRecord where
  kind : BoundaryKind
  quiver : Six
  returnVertex : Fin 4

structure ReturnRecord (size : Nat) where
  target : Fin (size+1)
  frame : Frame

/-- Backward positions 0,1,2 mean R:1, R:2, Q:0 respectively. -/
structure StripRecord (size : Nat) where
  m : Int
  a : Int
  b : Int
  c : Int
  rootCore : Fin (size+1)
  rootQuiver : Six
  rootWord : List (Fin 4)
  rootFrame : Frame
  backward : Fin 3 → ReturnRecord size

structure LocalRecord (size : Nat) where
  phase : Fin 2
  returnVertex : Fin 4
  frame : Frame
  alternateTarget : Fin (size+1)
  alternateFrame : Frame

inductive EdgeRecord (size stripCount : Nat) where
  | core (target : Fin (size+1)) (frame : Frame)
  | mstrip (strip : Fin stripCount) (index : Int) (state : Fin 6) (frame : Frame)
  | boundary (record : BoundaryRecord)
  | zero (x u v w : Int) (record : LocalRecord size)
  | pendant (d x y : Int) (record : LocalRecord size)

structure CoreRow (size stripCount : Nat) where
  quiver : Six
  word : List (Fin 4)
  edges : Fin 4 → EdgeRecord size stripCount

/-- `size+1` represents precisely a nonempty finite core. The two finite
functions are normalized versions of the uniquely numbered JSON record lists. -/
structure Certificate where
  initial : Six
  entryWord : List (Fin 4)
  entryFrame : Frame
  size : Nat
  stripCount : Nat
  core : Fin (size+1) → CoreRow size stripCount
  strips : Fin stripCount → StripRecord size
  triangleAvoidance : Bool

def Certificate.node (c : Certificate) (i : Fin (c.size+1)) : Matrix 4 :=
  (c.core i).quiver.matrix

end QuiverProofs.LStar
