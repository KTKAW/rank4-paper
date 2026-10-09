import QuiverProofs.TriangleRegions

set_option linter.unusedSimpArgs false
namespace QuiverProofs.E2Strip
open TriangleRegions Regions Forks

def Domain (a b c : Int) : Prop := 3 ≤ b ∧ b<c ∧ c<a
def A (a b c : Int) : Int := 6*a+3*b-2*c
def B (a c : Int) : Int := 2*a-c
def C (a b c : Int) : Int := 3*a+b-c
def D (a c : Int) : Int := 3*a-2*c
def U (a b : Int) : Int := a+b
def E (a b c : Int) : Int := 3*(A a b c)-U a b

def R (a b c : Int) : Matrix 4 := ofSix (-1) (-2) (a) (-1) (b) (-c)
def P (a b c : Int) : Matrix 4 := ofSix (1) (2) (-a) (-1) (U a b) (B a c)
def Q (a b c : Int) : Matrix 4 := ofSix (-1) (2) (b) (1) (-(U a b)) (C a b c)
def S (a b c : Int) : Matrix 4 := ofSix (3) (-2) (D a c) (1) (U a b) (-(B a c))
def T (a b c : Int) : Matrix 4 := ofSix (-3) (1) (A a b c) (-1) (-(U a b)) (-(B a c))
def V (a b c : Int) : Matrix 4 := ofSix (3) (-1) (-(A a b c)) (2) (E a b c) (-(B a c))

private theorem fin4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

theorem parameter_bounds (a b c : Int) (h : Domain a b c) :
    3≤a ∧ 3≤b ∧ 3≤c ∧ 3≤U a b ∧ 3≤B a c ∧ 3≤C a b c ∧
    3≤D a c ∧ 3≤A a b c ∧ 3≤E a b c ∧
    4*a < A a b c ∧ U a b < 2*a ∧ a < D a c ∧ a < B a c := by
  unfold Domain at h
  simp only [A,B,C,D,E,U]
  omega

theorem domain_forward (a b c : Int) (h : Domain a b c) :
    Domain (A a b c) (B a c) (C a b c) := by
  unfold Domain A B C at *
  omega

private theorem product_three (x y j : Int) (hx : 3≤x) (hy : 3≤y) (hj : j≤3) :
    x < x*y-j ∧ y < x*y-j := by
  have h1 := Int.mul_le_mul_of_nonneg_left hy (show 0≤x by omega)
  have h2 := Int.mul_le_mul_of_nonneg_right hx (show 0≤y by omega)
  constructor <;> omega

def frame3201 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | _ => 1),(fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0),by decide,by decide⟩

def frame3012 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0),by decide,by decide⟩

def frame3102 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | _ => 2),(fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0),by decide,by decide⟩

def frame0231 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1),(fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | _ => 2),by decide,by decide⟩

def frame3021 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | _ => 1),(fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0),by decide,by decide⟩

def frame1023 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3),by decide,by decide⟩

def frame3120 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),(fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | _ => 0),by decide,by decide⟩

def frame0213 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3),by decide,by decide⟩

def frame2013 : Relabeling 4 := ⟨(fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3),(fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3),by decide,by decide⟩

theorem r_3_root (a b c : Int) (h : Domain a b c) :
    IsRoot (mutate (R a b c) 3) 3 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (reverse (mutate (R a b c) 3)) frame3201 = root (-(-(c))) (-(-(a*c-2))) (-(-(b*c-1))) (-(-(-(-a)))) (-(-(-(-b)))) 1 := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame3201,mutate,ofSix,correction,R,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (R a b c) 3)) frame3201) 0 := by
    rw [heq]
    apply IsRoot.basic
    · simp only [Regions.Domain,A,B,C,D,E,U]; grind
    · exact Or.inr rfl
  exact root_of_reverse (root_of_relabel frame3201 hr)

theorem p_3_root (a b c : Int) (h : Domain a b c) :
    IsRoot (mutate (P a b c) 3) 3 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (reverse (mutate (P a b c) 3)) frame3012 = root (-(-(a))) (-(1-a*(U a b))) (-(2-a*(B a c))) (-(-(-(-(U a b))))) (-(-(-(-(B a c))))) 1 := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame3012,mutate,ofSix,correction,P,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsRoot (relabel (reverse (mutate (P a b c) 3)) frame3012) 0 := by
    rw [heq]
    apply IsRoot.basic
    · simp only [Regions.Domain,A,B,C,D,E,U]; grind
    · exact Or.inr rfl
  exact root_of_reverse (root_of_relabel frame3012 hr)

theorem q_3_fork (a b c : Int) (h : Domain a b c) :
    IsFork (mutate (Q a b c) 3) 3 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (mutate (Q a b c) 3) frame3102 = template (-(-(U a b))) (-(-b)) (-(-(C a b c))) (-(-(b*(U a b)-1))) (-(1-(C a b c)*(U a b))) (2) := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame3102,mutate,ofSix,correction,Q,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsFork (relabel (mutate (Q a b c) 3) frame3102) 0 := by
    rw [heq]
    apply IsFork.basic
    simp only [Forks.Domain,A,B,C,D,E,U]; grind
  exact fork_of_relabel frame3102 hr

theorem s_0_fork (a b c : Int) (h : Domain a b c) :
    IsFork (mutate (S a b c) 0) 0 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (reverse (mutate (S a b c) 0)) frame0231 = template (-(-(2))) (-(-(D a c))) (-(-3)) (-(-(4*a-3*c))) (-(-(-(-5)))) (-(-(U a b))) := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame0231,mutate,ofSix,correction,S,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsFork (relabel (reverse (mutate (S a b c) 0)) frame0231) 0 := by
    rw [heq]
    apply IsFork.basic
    simp only [Forks.Domain,A,B,C,D,E,U]; grind
  exact fork_of_reverse (fork_of_relabel frame0231 hr)

theorem s_3_fork (a b c : Int) (h : Domain a b c) :
    IsFork (mutate (S a b c) 3) 3 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (mutate (S a b c) 3) frame3201 = template (-(-(B a c))) (-(-(D a c))) (-(-(U a b))) (-(-((D a c)*(B a c)-2))) (-(-(1+(U a b)*(B a c)))) (3) := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame3201,mutate,ofSix,correction,S,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsFork (relabel (mutate (S a b c) 3) frame3201) 0 := by
    rw [heq]
    apply IsFork.basic
    simp only [Forks.Domain,A,B,C,D,E,U]; grind
  exact fork_of_relabel frame3201 hr

theorem t_3_root (a b c : Int) (h : Domain a b c) :
    IsRoot (mutate (T a b c) 3) 3 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (mutate (T a b c) 3) frame3021 = root (-(-(A a b c))) (1+(A a b c)*(B a c)) ((A a b c)*(U a b)-3) (-(-(B a c))) (-(-(U a b))) 1 := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame3021,mutate,ofSix,correction,T,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsRoot (relabel (mutate (T a b c) 3) frame3021) 0 := by
    rw [heq]
    apply IsRoot.basic
    · simp only [Regions.Domain,A,B,C,D,E,U]; grind
    · exact Or.inr rfl
  exact root_of_relabel frame3021 hr

theorem v_1_fork (a b c : Int) (h : Domain a b c) :
    IsFork (mutate (V a b c) 1) 1 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (reverse (mutate (V a b c) 1)) frame1023 = template (-(-(-(-3)))) (-(-2)) (-(-(E a b c))) (-(-(5))) (-(-(8*(A a b c)-3*(U a b)))) (-(-(B a c))) := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame1023,mutate,ofSix,correction,V,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsFork (relabel (reverse (mutate (V a b c) 1)) frame1023) 0 := by
    rw [heq]
    apply IsFork.basic
    simp only [Forks.Domain,A,B,C,D,E,U]; grind
  exact fork_of_reverse (fork_of_relabel frame1023 hr)

theorem v_3_root (a b c : Int) (h : Domain a b c) :
    IsRoot (mutate (V a b c) 3) 3 := by
  have hp := parameter_bounds a b c h
  have hm0 := product_three a c (2) (by omega) (by omega) (by decide)
  have hm1 := product_three b c (1) (by omega) (by omega) (by decide)
  have hm2 := product_three a (U a b) (1) (by omega) (by omega) (by decide)
  have hm3 := product_three a (B a c) (2) (by omega) (by omega) (by decide)
  have hm4 := product_three b (U a b) (1) (by omega) (by omega) (by decide)
  have hm5 := product_three (C a b c) (U a b) (1) (by omega) (by omega) (by decide)
  have hm6 := product_three (D a c) (B a c) (2) (by omega) (by omega) (by decide)
  have hm7 := product_three (U a b) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm8 := product_three (A a b c) (U a b) (3) (by omega) (by omega) (by decide)
  have hm9 := product_three (A a b c) (B a c) (-1) (by omega) (by omega) (by decide)
  have hm10 := product_three (A a b c) (E a b c) (3) (by omega) (by omega) (by decide)
  have hm11 := product_three (B a c) (E a b c) (-2) (by omega) (by omega) (by decide)
  simp only [A,B,C,D,E,U] at hp hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11
  have heq : relabel (mutate (V a b c) 3) frame3120 = root (-(-(E a b c))) (2+(B a c)*(E a b c)) (-(3-(A a b c)*(E a b c))) (-(-(B a c))) (-(-(A a b c))) 1 := by
    unfold Domain at h
    funext i j
    rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
      simp [relabel,reverse,frame3120,mutate,ofSix,correction,V,A,B,C,D,E,U,root,template] <;> grind
  have hr : IsRoot (relabel (mutate (V a b c) 3) frame3120) 0 := by
    rw [heq]
    apply IsRoot.basic
    · simp only [Regions.Domain,A,B,C,D,E,U]; grind
    · exact Or.inr rfl
  exact root_of_relabel frame3120 hr

theorem r_zero (a b c : Int) (h : Domain a b c) :
    mutate (R a b c) 0 = P a b c := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,R,P,A,B,C,D,E,U] <;> grind

theorem p_one (a b c : Int) (h : Domain a b c) :
    mutate (P a b c) 1 = Q a b c := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,P,Q,A,B,C,D,E,U] <;> grind

theorem p_two (a b c : Int) (h : Domain a b c) :
    mutate (P a b c) 2 = S a b c := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,P,S,A,B,C,D,E,U] <;> grind

theorem s_one (a b c : Int) (h : Domain a b c) :
    mutate (S a b c) 1 = T a b c := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,S,T,A,B,C,D,E,U] <;> grind

theorem t_zero (a b c : Int) (h : Domain a b c) :
    mutate (T a b c) 0 = V a b c := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,T,V,A,B,C,D,E,U] <;> grind

theorem q_two (a b c : Int) (h : Domain a b c) :
    mutate (Q a b c) 2 = R (A a b c) (B a c) (C a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,Q,R,A,B,C,D,E,U] <;> grind

theorem t_two (a b c : Int) (h : Domain a b c) :
    relabel (mutate (T a b c) 2) frame0213 = R (A a b c) (B a c) (C a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,frame0213,T,R,A,B,C,D,E,U] <;> grind

theorem v_two (a b c : Int) (h : Domain a b c) :
    relabel (mutate (V a b c) 2) frame2013 = Q (A a b c) (B a c) (C a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  funext i j
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp [mutate,ofSix,correction,relabel,frame2013,V,Q,A,B,C,D,E,U] <;> grind

theorem r_cyclic (a b c : Int) (h : Domain a b c) : ¬ Acyclic (R a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [R,ofSix,A,B,C,D,E,U] <;> omega)
  have h1 := hr 3 2 (by simp [R,ofSix,A,B,C,D,E,U] <;> omega)
  have h2 := hr 2 0 (by simp [R,ofSix,A,B,C,D,E,U] <;> omega)
  omega

theorem r_deletion (a b c : Int) (h : Domain a b c) : DeletionAcyclic (R a b c) 2 := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  refine ⟨fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 2,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [R,ofSix,A,B,C,D,E,U] <;> omega

theorem p_cyclic (a b c : Int) (h : Domain a b c) : ¬ Acyclic (P a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by simp [P,ofSix,A,B,C,D,E,U] <;> omega)
  have h1 := hr 1 3 (by simp [P,ofSix,A,B,C,D,E,U] <;> omega)
  have h2 := hr 3 0 (by simp [P,ofSix,A,B,C,D,E,U] <;> omega)
  omega

theorem p_deletion (a b c : Int) (h : Domain a b c) : DeletionAcyclic (P a b c) 0 := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  refine ⟨fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 0 | _ => 2,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [P,ofSix,A,B,C,D,E,U] <;> omega

theorem q_cyclic (a b c : Int) (h : Domain a b c) : ¬ Acyclic (Q a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  rintro ⟨rank,hr⟩
  have h0 := hr 0 3 (by simp [Q,ofSix,A,B,C,D,E,U] <;> omega)
  have h1 := hr 3 1 (by simp [Q,ofSix,A,B,C,D,E,U] <;> omega)
  have h2 := hr 1 0 (by simp [Q,ofSix,A,B,C,D,E,U] <;> omega)
  omega

theorem q_deletion (a b c : Int) (h : Domain a b c) : DeletionAcyclic (Q a b c) 1 := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  refine ⟨fun i => match i.val with | 0 => 0 | 1 => 0 | 2 => 1 | _ => 2,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [Q,ofSix,A,B,C,D,E,U] <;> omega

theorem s_cyclic (a b c : Int) (h : Domain a b c) : ¬ Acyclic (S a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by simp [S,ofSix,A,B,C,D,E,U] <;> omega)
  have h1 := hr 1 2 (by simp [S,ofSix,A,B,C,D,E,U] <;> omega)
  have h2 := hr 2 0 (by simp [S,ofSix,A,B,C,D,E,U] <;> omega)
  omega

theorem s_deletion (a b c : Int) (h : Domain a b c) : DeletionAcyclic (S a b c) 2 := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  refine ⟨fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 0 | _ => 2,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [S,ofSix,A,B,C,D,E,U] <;> omega

theorem t_cyclic (a b c : Int) (h : Domain a b c) : ¬ Acyclic (T a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  rintro ⟨rank,hr⟩
  have h0 := hr 0 2 (by simp [T,ofSix,A,B,C,D,E,U] <;> omega)
  have h1 := hr 2 1 (by simp [T,ofSix,A,B,C,D,E,U] <;> omega)
  have h2 := hr 1 0 (by simp [T,ofSix,A,B,C,D,E,U] <;> omega)
  omega

theorem t_deletion (a b c : Int) (h : Domain a b c) : DeletionAcyclic (T a b c) 1 := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  refine ⟨fun i => match i.val with | 0 => 0 | 1 => 0 | 2 => 2 | _ => 1,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [T,ofSix,A,B,C,D,E,U] <;> omega

theorem v_cyclic (a b c : Int) (h : Domain a b c) : ¬ Acyclic (V a b c) := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  rintro ⟨rank,hr⟩
  have h0 := hr 0 1 (by simp [V,ofSix,A,B,C,D,E,U] <;> omega)
  have h1 := hr 1 2 (by simp [V,ofSix,A,B,C,D,E,U] <;> omega)
  have h2 := hr 2 0 (by simp [V,ofSix,A,B,C,D,E,U] <;> omega)
  omega

theorem v_deletion (a b c : Int) (h : Domain a b c) : DeletionAcyclic (V a b c) 0 := by
  have hp := parameter_bounds a b c h
  unfold Domain at h
  simp only [A,B,C,D,E,U] at hp
  refine ⟨fun i => match i.val with | 0 => 0 | 1 => 0 | 2 => 2 | _ => 1,?_⟩
  intro i j hi hj hij
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [V,ofSix,A,B,C,D,E,U] <;> omega

end QuiverProofs.E2Strip
