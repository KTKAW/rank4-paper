import QuiverProofs.Mutation
import Init.Data.Vector.Lemmas

/-! Materialize finite matrix entries during computation. All cached values
are proved equal to the original matrices; this changes evaluation cost only. -/
namespace QuiverProofs.MatrixCache

def snapshot {n : Nat} (B : Matrix n) : Matrix n :=
  let rows := Vector.ofFn (fun i => Vector.ofFn (B i))
  fun i j => (rows.get i).get j

theorem snapshot_eq {n : Nat} (B : Matrix n) : snapshot B = B := by
  funext i j
  simp [snapshot,Vector.get]

/-- The polymorphic result and noinline boundary keep the compiler from
eta-expanding matrix materialization into every entry lookup. -/
@[noinline] def withSnapshot {n : Nat} {α : Type} (B : Matrix n)
    (next : Matrix n → α) : α :=
  let rows := Vector.ofFn (fun i => Vector.ofFn (B i))
  next (fun i j => (rows.get i).get j)

theorem withSnapshot_eq {n : Nat} {α : Type} (B : Matrix n)
    (next : Matrix n → α) : withSnapshot B next = next B := by
  have h : (fun i j => ((Vector.ofFn (fun i => Vector.ofFn (B i))).get i).get j) = B := by
    funext i j
    simp [Vector.get]
  exact congrArg next h

/-- Evaluate a matrix predicate after materializing its input once. -/
def cachedDecidable {n : Nat} (P : Matrix n → Prop)
    (test : ∀ B, Decidable (P B)) (B : Matrix n) : Decidable (P B) :=
  decidable_of_iff (withSnapshot B (fun C => @decide (P C) (test C)) = true)
    (by simp only [withSnapshot_eq,decide_eq_true_eq])

def cachedMutate {n : Nat} (B : Matrix n) (k : Fin n) : Matrix n :=
  withSnapshot B (fun C => withSnapshot (mutate C k) (fun D => D))

theorem cachedMutate_eq {n : Nat} (B : Matrix n) (k : Fin n) :
    cachedMutate B k = mutate B k := by simp only [cachedMutate,withSnapshot_eq]

/-- Replay a word with materialized intermediate matrices, then evaluate the
continuation before exposing any function-valued endpoint. -/
@[noinline] def withWord {n : Nat} {α : Type} (B : Matrix n) :
    List (Fin n) → (Matrix n → α) → α
  | [], next => withSnapshot B next
  | k :: ks, next => withSnapshot B (fun C => withWord (mutate C k) ks next)

theorem withWord_eq {n : Nat} {α : Type} (B : Matrix n)
    (word : List (Fin n)) (next : Matrix n → α) :
    withWord B word next = next (applyWord B word) := by
  induction word generalizing B with
  | nil => simp only [withWord,withSnapshot_eq,applyWord]
  | cons k ks ih => simp only [withWord,withSnapshot_eq,ih,applyWord]

def cachedWord {n : Nat} (B : Matrix n) : List (Fin n) → Matrix n
  | [] => withSnapshot B (fun C => C)
  | k :: ks => withSnapshot B (fun C =>
      withSnapshot (mutate C k) (fun D => cachedWord D ks))

theorem cachedWord_eq {n : Nat} (B : Matrix n) (word : List (Fin n)) :
    cachedWord B word = applyWord B word := by
  induction word generalizing B with
  | nil => simp only [cachedWord,withSnapshot_eq,applyWord]
  | cons k ks ih => simp only [cachedWord,withSnapshot_eq,ih,applyWord]

end QuiverProofs.MatrixCache
