import QuiverProofs.ProperMutation

/-! Rank-four representative independence of proper mutation. A sign surrogate
uses maximal mutation support; transfer applies to arbitrary integer weights. -/
namespace QuiverProofs.ProperMutationRepresentativeChoice
open ProperOrder ProperWiggle ProperMutation ProperWiggleInvariants Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def signProxy (x : Int) : Int := if x < 0 then -2 else if x = 0 then 0 else 2

theorem signProxy_zero (x : Int) : signProxy x = 0 ↔ x = 0 := by
  unfold signProxy
  split <;> (try split) <;> omega

theorem signProxy_nonpos (x : Int) : signProxy x ≤ 0 ↔ x ≤ 0 := by
  unfold signProxy
  split <;> (try split) <;> omega

theorem signProxy_nonneg (x : Int) : 0 ≤ signProxy x ↔ 0 ≤ x := by
  unfold signProxy
  split <;> (try split) <;> omega

theorem signProxy_neg (x : Int) : signProxy (-x) = -signProxy x := by
  unfold signProxy
  repeat' split <;> omega

def proxyMatrix (B : Matrix 4) : Matrix 4 := fun i j => signProxy (B i j)

theorem proxy_skew (B : Matrix 4) (hB : SkewSymmetric B) :
    SkewSymmetric (proxyMatrix B) := by
  intro i j
  simp only [proxyMatrix,hB i j,signProxy_neg]

theorem structural_zero (x y z : Int)
    (h : signProxy z + correction (signProxy x) (signProxy y) = 0) :
    z + correction x y = 0 := by
  by_cases hx : x < 0 <;> by_cases hx0 : x = 0 <;>
    by_cases hy : y < 0 <;> by_cases hy0 : y = 0 <;>
    by_cases hz : z < 0 <;> by_cases hz0 : z = 0 <;>
    simp [signProxy,hx,hx0,hy,hy0,hz,hz0,correction,Int.max_def] at h ⊢ <;>
    grind

theorem proxy_mutation_zero (B : Matrix 4) (k i j : Fin 4)
    (h : mutate (proxyMatrix B) k i j = 0) : mutate B k i j = 0 := by
  by_cases hi : i=k
  · simp [mutate,hi,proxyMatrix] at h ⊢
    exact (signProxy_zero _).mp h
  · by_cases hj : j=k
    · simp [mutate,hi,hj,proxyMatrix] at h ⊢
      exact (signProxy_zero _).mp h
    · simp only [mutate,hi,hj,or_self,if_false,proxyMatrix] at h ⊢
      exact structural_zero _ _ _ h

theorem wiggle_zero_transfer (S B : Matrix 4)
    (hz : ∀ i j, S i j=0 → B i j=0) {p q : CyclicOrder}
    (h : WiggleEquivalent S p q) : WiggleEquivalent B p q := by
  induction h with
  | same h => exact .same h
  | step h =>
    obtain ⟨r,a,hp,ha,hq⟩ := h
    exact .step ⟨r,a,hp,hz _ _ ha,hq⟩
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem wiggle_proxy (B : Matrix 4) {p q : CyclicOrder}
    (h : WiggleEquivalent B p q) : WiggleEquivalent (proxyMatrix B) p q :=
  wiggle_zero_transfer B (proxyMatrix B)
    (fun i j h => (signProxy_zero _).mpr h) h

theorem cut_proxy (B : Matrix 4) (r : CyclicOrder) (c : Fin 4) :
    Cut (proxyMatrix B) r c ↔ Cut B r c := by
  have hc : c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by omega
  rcases hc with rfl|rfl|rfl|rfl <;>
    simp [Cut,proxyMatrix,signProxy_nonpos,signProxy_nonneg]

def ternaryValue (x : Fin 3) : Int := if x=0 then -2 else if x=1 then 0 else 2

def digit (code : Fin 729) (place : Nat) : Fin 3 :=
  ⟨code.val / place % 3, Nat.mod_lt _ (by decide)⟩

def pattern (code : Fin 729) : Matrix 4 :=
  ofSix (ternaryValue (digit code 1)) (ternaryValue (digit code 3))
    (ternaryValue (digit code 9)) (ternaryValue (digit code 27))
    (ternaryValue (digit code 81)) (ternaryValue (digit code 243))

def ternaryCode (x : Int) : Fin 3 := if x < 0 then 0 else if x=0 then 1 else 2

def encode (s : Fin 6 → Fin 3) : Fin 729 :=
  ⟨(s 0).val+3*(s 1).val+9*(s 2).val+27*(s 3).val+81*(s 4).val+243*(s 5).val,
    by have := (s 0).isLt; have := (s 1).isLt; have := (s 2).isLt
       have := (s 3).isLt; have := (s 4).isLt; have := (s 5).isLt; omega⟩

theorem encode_digits : ∀ s : Fin 6 → Fin 3,
    digit (encode s) 1=s 0 ∧ digit (encode s) 3=s 1 ∧
    digit (encode s) 9=s 2 ∧ digit (encode s) 27=s 3 ∧
    digit (encode s) 81=s 4 ∧ digit (encode s) 243=s 5 := by
  intro s
  have := (s 0).isLt; have := (s 1).isLt; have := (s 2).isLt
  have := (s 3).isLt; have := (s 4).isLt; have := (s 5).isLt
  repeat' apply And.intro
  all_goals apply Fin.ext
  all_goals simp only [digit,encode]
  all_goals omega

theorem ternaryCode_value (x : Int) : ternaryValue (ternaryCode x)=signProxy x := by
  unfold ternaryValue ternaryCode signProxy
  split <;> split <;> simp_all

theorem proxy_pattern (B : Matrix 4) (hB : SkewSymmetric B) :
    ∃ code : Fin 729, proxyMatrix B=pattern code := by
  let s : Fin 6 → Fin 3 := fun i => match i.val with
    | 0 => ternaryCode (B 0 1) | 1 => ternaryCode (B 0 2)
    | 2 => ternaryCode (B 0 3) | 3 => ternaryCode (B 1 2)
    | 4 => ternaryCode (B 1 3) | _ => ternaryCode (B 2 3)
  refine ⟨encode s, ?_⟩
  have hd := encode_digits s
  rw [← ofSix_reconstruct (proxyMatrix B) (proxy_skew B hB)]
  simp only [pattern,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2]
  simp [s,proxyMatrix,ternaryCode_value]

def firstIndex (k : Fin 4) (i : Fin 6) : Fin 24 := ⟨k.val*6+i.val, by omega⟩
def firstOrder (k : Fin 4) (i : Fin 6) : CyclicOrder := permutation (firstIndex k i)

private theorem order_eq_of_toFun_eq (p q : CyclicOrder)
    (h : p.toFun=q.toFun) : p=q := by
  have hi : p.invFun=q.invFun := by
    funext i
    apply p.injective
    rw [p.right_inv,h,q.right_inv]
  cases p
  cases q
  simp_all

theorem first_order_exhaustive (r : CyclicOrder) (k : Fin 4) (h : r.toFun 0=k) :
    ∃ i : Fin 6, r=firstOrder k i := by
  obtain ⟨a,ha⟩ := permutation_exhaustive r
  have ht : ∀ (a : Fin 24) (k : Fin 4), (permutation a).toFun 0=k →
      ∃ i : Fin 6, ∀ v, (permutation a).toFun v=(firstOrder k i).toFun v := by decide
  obtain ⟨i,hi⟩ := ht a k (by rw [←ha]; exact h)
  exact ⟨i,order_eq_of_toFun_eq _ _ (ha.trans (funext hi))⟩

private def resultData : Table (Fin 6) := (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.leaf 4)) (.branch (.branch (.leaf 4) (.leaf 3)) (.leaf 1))) (.branch (.branch (.branch (.leaf 2) (.leaf 0)) (.leaf 2)) (.branch (.branch (.leaf 3) (.leaf 1)) (.leaf 5)))) (.branch (.branch (.branch (.branch (.leaf 1) (.leaf 3)) (.leaf 0)) (.branch (.branch (.leaf 5) (.leaf 4)) (.leaf 4))) (.branch (.branch (.branch (.leaf 3) (.leaf 2)) (.leaf 1)) (.branch (.branch (.leaf 5) (.leaf 5)) (.leaf 2))))) (.branch (.branch (.branch (.branch (.branch (.leaf 4) (.leaf 2)) (.leaf 1)) (.branch (.branch (.leaf 3) (.leaf 5)) (.leaf 0))) (.branch (.branch (.branch (.leaf 5) (.leaf 1)) (.leaf 0)) (.branch (.branch (.leaf 2) (.leaf 4)) (.leaf 3)))) (.branch (.branch (.branch (.branch (.leaf 2) (.leaf 4)) (.leaf 3)) (.branch (.branch (.leaf 1) (.leaf 0)) (.leaf 5))) (.branch (.branch (.branch (.leaf 0) (.leaf 3)) (.leaf 5)) (.branch (.branch (.leaf 4) (.leaf 2)) (.leaf 1)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf 3) (.leaf 1)) (.leaf 5)) (.branch (.branch (.leaf 0) (.leaf 2)) (.leaf 2))) (.branch (.branch (.branch (.leaf 1) (.leaf 4)) (.leaf 3)) (.branch (.branch (.leaf 0) (.leaf 0)) (.leaf 4)))) (.branch (.branch (.branch (.branch (.leaf 5) (.leaf 5)) (.leaf 2)) (.branch (.branch (.leaf 2) (.leaf 1)) (.leaf 3))) (.branch (.branch (.branch (.leaf 4) (.leaf 5)) (.leaf 4)) (.branch (.branch (.leaf 1) (.leaf 3)) (.leaf 0))))) (.branch (.branch (.branch (.branch (.branch (.leaf 0) (.leaf 0)) (.leaf 4)) (.branch (.branch (.leaf 4) (.leaf 3)) (.leaf 1))) (.branch (.branch (.branch (.leaf 2) (.leaf 0)) (.leaf 2)) (.branch (.branch (.leaf 3) (.leaf 1)) (.leaf 5)))) (.branch (.branch (.branch (.branch (.leaf 1) (.leaf 3)) (.leaf 0)) (.branch (.branch (.leaf 5) (.leaf 4)) (.leaf 4))) (.branch (.branch (.branch (.leaf 3) (.leaf 2)) (.leaf 1)) (.branch (.branch (.leaf 5) (.leaf 5)) (.leaf 2)))))))

def resultIndex (k : Fin 4) (i : Fin 6) (c : Fin 4) : Fin 6 :=
  resultData.get ((k.val*6+i.val)*4+c.val)

theorem result_correct : ∀ (k : Fin 4) (i : Fin 6) (c : Fin 4),
    SameCyclicOrder ((firstOrder k i).trans (cutOrder c)) (order (resultIndex k i c)) := by decide

instance (B : Matrix 4) (r : CyclicOrder) (c : Fin 4) : Decidable (Cut B r c) := by
  unfold Cut
  dsimp only
  split <;> infer_instance



end QuiverProofs.ProperMutationRepresentativeChoice
