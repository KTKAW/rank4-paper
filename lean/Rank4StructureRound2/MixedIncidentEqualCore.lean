import Mathlib.Tactic.Ring
import Rank4Round2.MultiRegionInterfaces
namespace QuiverProofs.Rank4StructureRound2.MixedIncidentEqualCore
open MultiPolynomialCertificate MultiRegionInterfaces RecursiveRegions Forks Regions
set_option maxHeartbeats 24000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace EqualSlopeModule
def perm0 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3),by decide,by decide⟩
def perm1 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 2),by decide,by decide⟩
def perm2 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),by decide,by decide⟩
def perm3 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),by decide,by decide⟩
def perm4 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),by decide,by decide⟩
def perm5 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | _ => 1),by decide,by decide⟩
def perm6 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),by decide,by decide⟩
def perm7 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2),by decide,by decide⟩
def perm8 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),by decide,by decide⟩
def perm9 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2),by decide,by decide⟩
def perm10 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2),(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1),by decide,by decide⟩
def perm11 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1),by decide,by decide⟩
def perm12 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),by decide,by decide⟩
def perm13 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1),(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | _ => 2),by decide,by decide⟩
def perm14 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3),by decide,by decide⟩
def perm15 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2),by decide,by decide⟩
def perm16 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1),by decide,by decide⟩
def perm17 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1),by decide,by decide⟩
def perm18 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0),by decide,by decide⟩
def perm19 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0),by decide,by decide⟩
def perm20 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0),by decide,by decide⟩
def perm21 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),by decide,by decide⟩
def perm22 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0),by decide,by decide⟩
def perm23 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0),by decide,by decide⟩

namespace EqualSlope
private theorem finCore (i : Fin 2) : i=0 ∨ i=1 := by omega
def pnode (i : Fin 2) : PMatrix := match i.val with
  | 0 => six [(1,0,0,0)] [(-1,0,0,0)] [(-2,0,0,0),(-1,1,0,0)] [(2,0,0,0)] [(-7,0,0,0),(-1,0,1,0),(-3,1,0,0),(-1,2,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)]
  | _ => six [(-1,0,0,0)] [(1,0,0,0)] [(2,0,0,0),(1,1,0,0)] [(1,0,0,0)] [(-9,0,0,0),(-1,0,1,0),(-4,1,0,0),(-1,2,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)]
def node (t : Point) (i : Fin 2) : Matrix 4 := matrix (pnode i) t
def Core (t : Point) (B : Matrix 4) : Prop := ∃ i, B=node t i
abbrev SafeCore (t : Point) := Safe data (Core t)
theorem node_safe (t : Point) (i : Fin 2) : SafeCore t (node t i) := Safe.central ⟨i,rfl⟩
theorem node_skew (t : Point) (i : Fin 2) : SkewSymmetric (node t i) := by
  rcases finCore i with rfl|rfl <;> simp only [node,pnode,matrix_six] <;> exact ofSix_skew _ _ _ _ _ _
theorem cyclic0 (t : Point) (ht : ∀ i,0≤t i) : ¬Acyclic (node t 0) := by
  rintro ⟨rank,hr⟩
  have h0:=hr 0 1 (pos (pnode 0 0 1) t ht (by decide))
  have h1:=hr 1 2 (pos (pnode 0 1 2) t ht (by decide))
  have h2:=hr 2 0 (pos (pnode 0 2 0) t ht (by decide))
  omega
theorem edge0_0 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 0) 0) := by
  have he:=mutation_equal (pnode 0) (prelabel (pnode 1) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 1) perm0.symm
theorem edge0_1 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 0) 1) := by
  have he:=mutation_equal (pnode 0) (prelabel (pnode 0) perm2.symm) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 1)
  rw [he]
  exact Safe.framed (node_safe t 0) perm2.symm
theorem edge0_2 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 0) 2) := by
  have he:=mutation_equal (pnode 0) (prelabel (pnode 0) perm2.symm) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 0) t) 2)
  rw [he]
  exact Safe.framed (node_safe t 0) perm2.symm
theorem edge0_3 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 0) 3) := by
  have he:=mutation_equal (pnode 0) (prelabel (root [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(15,0,0,0),(2,0,1,0),(13,1,0,0),(1,1,1,0),(5,2,0,0),(1,3,0,0)] [(47,0,0,0),(14,0,1,0),(1,0,2,0),(42,1,0,0),(6,1,1,0),(23,2,0,0),(2,2,1,0),(6,3,0,0),(1,4,0,0)] [(2,0,0,0),(1,1,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(1,0,0,0)]) perm22.symm) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 0) 3
  rw [show mutate (node t 0) 3=(relabel (matrix (root [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(15,0,0,0),(2,0,1,0),(13,1,0,0),(1,1,1,0),(5,2,0,0),(1,3,0,0)] [(47,0,0,0),(14,0,1,0),(1,0,2,0),(42,1,0,0),(6,1,1,0),(23,2,0,0),(2,2,1,0),(6,3,0,0),(1,4,0,0)] [(2,0,0,0),(1,1,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(1,0,0,0)]) t) perm22.symm) from he]
  exact IsRoot.relabelled (root_sound [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(15,0,0,0),(2,0,1,0),(13,1,0,0),(1,1,1,0),(5,2,0,0),(1,3,0,0)] [(47,0,0,0),(14,0,1,0),(1,0,2,0),(42,1,0,0),(6,1,1,0),(23,2,0,0),(2,2,1,0),(6,3,0,0),(1,4,0,0)] [(2,0,0,0),(1,1,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(1,0,0,0)] t ht (by decide)) perm22.symm
theorem cyclic1 (t : Point) (ht : ∀ i,0≤t i) : ¬Acyclic (node t 1) := by
  rintro ⟨rank,hr⟩
  have h0:=hr 0 3 (pos (pnode 1 0 3) t ht (by decide))
  have h1:=hr 3 1 (pos (pnode 1 3 1) t ht (by decide))
  have h2:=hr 1 0 (pos (pnode 1 1 0) t ht (by decide))
  omega
theorem edge1_0 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 1) 0) := by
  have he:=mutation_equal (pnode 1) (prelabel (pnode 0) perm0.symm) 0 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 0)
  rw [he]
  exact Safe.framed (node_safe t 0) perm0.symm
theorem edge1_1 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 1) 1) := by
  have he:=mutation_equal (pnode 1) (preverse (prelabel (pnode 1) perm14.symm)) 1 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 1)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 1) perm14.symm)
theorem edge1_2 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 1) 2) := by
  have he:=mutation_equal (pnode 1) (preverse (prelabel (pnode 1) perm6.symm)) 2 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  change SafeCore t (mutate (matrix (pnode 1) t) 2)
  rw [he]
  exact Safe.reversed (Safe.framed (node_safe t 1) perm6.symm)
theorem edge1_3 (t : Point) (ht : ∀ i,0≤t i) : SafeCore t (mutate (node t 1) 3) := by
  have he:=mutation_equal (pnode 1) (preverse (prelabel (root [(9,0,0,0),(1,0,1,0),(4,1,0,0),(1,2,0,0)] [(62,0,0,0),(16,0,1,0),(1,0,2,0),(55,1,0,0),(7,1,1,0),(28,2,0,0),(2,2,1,0),(7,3,0,0),(1,4,0,0)] [(17,0,0,0),(2,0,1,0),(17,1,0,0),(1,1,1,0),(6,2,0,0),(1,3,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(2,0,0,0),(1,1,0,0)] [(1,0,0,0)]) perm21.symm)) 3 t ht (by decide) (by decide)
  simp only [matrix_relabel,matrix_reverse] at he
  apply attach_root data (Core t) (node_safe t 1) 3
  rw [show mutate (node t 1) 3=(reverse (relabel (matrix (root [(9,0,0,0),(1,0,1,0),(4,1,0,0),(1,2,0,0)] [(62,0,0,0),(16,0,1,0),(1,0,2,0),(55,1,0,0),(7,1,1,0),(28,2,0,0),(2,2,1,0),(7,3,0,0),(1,4,0,0)] [(17,0,0,0),(2,0,1,0),(17,1,0,0),(1,1,1,0),(6,2,0,0),(1,3,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(2,0,0,0),(1,1,0,0)] [(1,0,0,0)]) t) perm21.symm)) from he]
  exact IsRoot.reversed (IsRoot.relabelled (root_sound [(9,0,0,0),(1,0,1,0),(4,1,0,0),(1,2,0,0)] [(62,0,0,0),(16,0,1,0),(1,0,2,0),(55,1,0,0),(7,1,1,0),(28,2,0,0),(2,2,1,0),(7,3,0,0),(1,4,0,0)] [(17,0,0,0),(2,0,1,0),(17,1,0,0),(1,1,1,0),(6,2,0,0),(1,3,0,0)] [(7,0,0,0),(1,0,1,0),(3,1,0,0),(1,2,0,0)] [(2,0,0,0),(1,1,0,0)] [(1,0,0,0)] t ht (by decide)) perm21.symm)
theorem NMA (t : Point) (ht : ∀ i,0≤t i) : ¬MutationAcyclic (node t 0) := by
  apply safe_NMA data rules (Core t)
  · rintro B ⟨i,rfl⟩;exact node_skew t i
  · rintro B ⟨i,rfl⟩;rcases finCore i with rfl|rfl
    · exact cyclic0 t ht
    · exact cyclic1 t ht
  · rintro B ⟨i,rfl⟩ k
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases finCore i with rfl|rfl <;> rcases hk with rfl|rfl|rfl|rfl
    · exact edge0_0 t ht
    · exact edge0_1 t ht
    · exact edge0_2 t ht
    · exact edge0_3 t ht
    · exact edge1_0 t ht
    · exact edge1_1 t ht
    · exact edge1_2 t ht
    · exact edge1_3 t ht
  · exact node_safe t 0
end EqualSlope
private theorem fin3 (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by omega
theorem family_NMA (t F : Int) (ht : 2≤t) (hF : t^2+5≤F) :
    ¬MutationAcyclic (ofSix 1 (-1) (-t) 2 (t-F) (F-t)) := by
  let point : Point := fun i => if i=0 then t-2 else if i=1 then F-t^2-5 else 0
  have hp : ∀ i,0≤point i := by
    intro i
    rcases fin3 i with rfl|rfl|rfl <;> simp [point] <;> omega
  have h:=EqualSlope.NMA point hp
  have he : EqualSlope.node point 0=ofSix 1 (-1) (-t) 2 (t-F) (F-t) := by
    simp only [EqualSlope.node,EqualSlope.pnode,matrix_six]
    congr 1 <;> simp [eval,weight,point,Int.pow_succ] <;> ring
  rwa [he] at h
#print axioms family_NMA
end EqualSlopeModule
end QuiverProofs.Rank4StructureRound2.MixedIncidentEqualCore

