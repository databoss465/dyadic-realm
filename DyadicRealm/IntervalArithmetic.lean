import Mathlib
open Dyadic Finset
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.unusedVariables false
set_option linter.style.longLine false

structure DyadIntvRep where
  a : ℤ
  b : ℤ
  n : ℕ
deriving DecidableEq

namespace DyadIntvRep

def left (I : DyadIntvRep) : Dyadic := Dyadic.ofIntWithPrec I.a I.n
def right (I : DyadIntvRep) : Dyadic := Dyadic.ofIntWithPrec I.b I.n

def add (I J : DyadIntvRep) : DyadIntvRep :=
  let n' := max I.n J.n
  let a' := I.a * (2 ^ (n' - I.n)) + J.a * (2 ^ (n' - J.n))
  let b' := I.b * (2 ^ (n' - I.n)) + J.b * (2 ^ (n' - J.n))
  -- have h : a' ≤ b' := by
  --   unfold a' b'
  --   apply Int.add_le_add
  --   · rw[Int.mul_le_mul_iff_of_pos_right]
  --     · exact I.isValid
  --     · refine Int.pow_pos ?_
  --       exact Int.sign_eq_one_iff_pos.mp rfl
  --   · rw[Int.mul_le_mul_iff_of_pos_right]
  --     · exact J.isValid
  --     · refine Int.pow_pos ?_
  --       exact Int.sign_eq_one_iff_pos.mp rfl
  ⟨a', b', n'⟩

instance : Add DyadIntvRep where
  add := DyadIntvRep.add

def neg (I : DyadIntvRep) : DyadIntvRep :=
  ⟨-I.b, -I.a, I.n⟩

instance : Neg DyadIntvRep where
  neg := DyadIntvRep.neg

def sub (I J : DyadIntvRep) : DyadIntvRep :=
  I + (-J)

instance : Sub DyadIntvRep where
  sub := DyadIntvRep.sub

def mul (I J : DyadIntvRep) : DyadIntvRep :=
  let a' := min (min (I.a*J.a) (I.a*J.b)) (min (I.b*J.a) (I.b*J.b))
  let b' := max (max (I.a*J.a) (I.a*J.b)) (max (I.b*J.a) (I.b*J.b))
  -- have h : a' ≤ b' := by
  --   unfold a' b'
  --   refine Left.min_le_max_of_add_le_add ?_
  --   apply add_le_add
  --   · exact min_le_max
  --   · exact min_le_max
  ⟨a', b', (I.n+J.n)⟩

instance : Mul DyadIntvRep where
  mul := DyadIntvRep.mul

def equiv (I J : DyadIntvRep) : Prop :=
  (I.left = J.left) ∧ (I.right = J.right)

instance : Setoid DyadIntvRep where
  r := DyadIntvRep.equiv
  iseqv := by
    constructor
    · intro I
      simp only [equiv, and_self]
    · intro I J h
      unfold equiv at *
      constructor
      · exact h.left.symm
      · exact h.right.symm
    · intro I J K h₁ h₂
      unfold equiv at *
      constructor
      · exact Eq.trans h₁.left h₂.left
      · exact Eq.trans h₁.right h₂.right

--Not really needed for proofs; only for computation
instance : DecidableRel equiv := by --∀ I J, Decidable (I.equiv J)
  intro I J
  exact instDecidableAnd

instance : DecidableRel fun (I J : DyadIntvRep) ↦ (I ≈ J) := by
  intro I J
  simp only[HasEquiv.Equiv]
  exact instDecidableAnd

@[simp]
lemma equiv_iff (I J : DyadIntvRep) : I ≈ J ↔ (I.left = J.left) ∧ (I.right = J.right) := by rfl

-- @[simp]
-- lemma add_right (I J : DyadIntvRep) : (I + J).right = I.right + J.right := by
--   sorry

-- @[simp]
-- lemma add_left (I J : DyadIntvRep) : (I + J).left = I.left + J.left := by
--   sorry

-- theorem add_comm : ∀ I J : DyadIntvRep, I + J ≈ J + I := by
--   intro I J
--   rw [equiv_iff]
--   constructor
--   · rw [add_left, add_left, Rat.add_comm]
--   · rw [add_right, add_right, Rat.add_comm]

lemma left_well_defined : ∀ (I J : DyadIntvRep), I ≈ J → I.left = J.left := by
  intro I J h
  simp only [equiv_iff] at h
  exact h.left

lemma right_well_defined :  ∀ (I J : DyadIntvRep), I ≈ J → I.right = J.right := by
  intro I J h
  simp only [equiv_iff] at h
  exact h.right

--NOT TRUE
-- We are only guaranteed a₁.add b₁ ≈ a₂.add b₂
-- lemma add_well_defined : ∀ (a₁ b₁ a₂ b₂ : DyadIntvRep),
--   a₁ ≈ a₂ → b₁ ≈ b₂ → a₁.add b₁ = a₂.add b₂ := by
--   sorry
end DyadIntvRep

---------------------------------------------------------------------

instance : LinearOrder Dyadic where
le_refl := Dyadic.le_refl
le_trans _ _ _ := Dyadic.le_trans
le_antisymm _ _ := Dyadic.le_antisymm
le_total := Dyadic.le_total
toDecidableLE := by exact fun _ _ => inferInstanceAs (Decidable (_ = true))
lt_iff_le_not_ge := by
  simp only [Dyadic.not_lt, iff_and_self]
  intro a b h
  apply Std.le_of_lt h

-- #synth AddGroup Dyadic
-- #synth LE Dyadic
-- #synth AddLeftMono Dyadic
-- #synth AddRightMono Dyadic
-- #check neg_le

namespace Dyadic

@[simp]
theorem add_le_add' {a b c d : Dyadic} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  simp only [le_iff_toRat, toRat_add] at *
  exact add_le_add h₁ h₂

@[simp]
lemma neg_le_iff {a b : Dyadic} : -a ≤ b ↔ -b ≤ a := by
  simp only [le_iff_toRat, toRat_neg]
  exact neg_le

@[simp]
lemma le_neg_iff {a b : Dyadic} : a ≤ -b ↔ b ≤ -a := by
  simp only [le_iff_toRat, toRat_neg]
  exact le_neg

@[simp]
lemma sub_eq_add_neg (a b : Dyadic) : a - b = a + (-b) := by rfl

lemma neg_min'_neg (S S' : Finset Dyadic) (hS : S.Nonempty) (hS' : S'.Nonempty)
(hS₁ : ∀ s ∈ S', -s ∈ S) (hS₂ : ∀ s ∈ S, -s ∈ S') : S.min' hS = -(S'.max' hS') := by
  rw [min'_eq_iff]
  constructor
  · apply hS₁
    apply max'_mem
  · intro s hs
    specialize hS₂ s hs
    rw [neg_le_iff]
    apply le_max'
    exact hS₂

lemma neg_max'_neg (S S' : Finset Dyadic) (hS : S.Nonempty) (hS' : S'.Nonempty)
(hS₁ : ∀ s ∈ S', -s ∈ S) (hS₂ : ∀ s ∈ S, -s ∈ S') : S.max' hS = -(S'.min' hS') := by
  rw [max'_eq_iff]
  constructor
  · apply hS₁
    apply min'_mem
  · intro s hs
    specialize hS₂ s hs
    rw [le_neg_iff]
    apply min'_le
    exact hS₂

end Dyadic

structure DyadicInterval where
  left : Dyadic
  right : Dyadic
  isValid : left ≤ right
  deriving DecidableEq

---------------------------------------------------------------------
namespace DyadicInterval
section
variable (I J K : DyadicInterval)(a : Dyadic)


def ofDyadic (a : Dyadic) : DyadicInterval := ⟨a, a, le_rfl⟩

instance : Coe Dyadic DyadicInterval := ⟨DyadicInterval.ofDyadic⟩

instance (n : Nat) : OfNat DyadicInterval n :=
  ⟨((n : Dyadic) : DyadicInterval)⟩

instance : NatCast DyadicInterval :=
  ⟨fun n => ((n : Dyadic) : DyadicInterval)⟩

instance : IntCast DyadicInterval :=
  ⟨fun z => ((z : Dyadic) : DyadicInterval)⟩

def Mem (x : ℝ) : Prop := I.left.toRat ≤ x ∧ x ≤ I.right.toRat
-- def Mem (x : Dyadic) : Prop := x ∈ Icc (I.left.toRat) (I.right.toRat)    Fix this?

instance : Membership ℝ DyadicInterval where mem := DyadicInterval.Mem

-- instance {x : ℝ} : Decidable (x ∈ I) := sorry

def add : DyadicInterval :=
  let l := I.left + J.left
  let r := I.right + J.right
  have h : l ≤ r := add_le_add' I.isValid J.isValid
  ⟨l, r, h⟩

instance : Add DyadicInterval := ⟨DyadicInterval.add⟩

def neg (I : DyadicInterval) : DyadicInterval :=
  have h : -I.right ≤ -I.left := by
     simp only [le_iff_toRat, toRat_neg, neg_le_neg_iff]
     rw [← le_iff_toRat]
     exact I.isValid
  ⟨-I.right, -I.left, h⟩

instance : Neg DyadicInterval := ⟨DyadicInterval.neg⟩

def sub : DyadicInterval := I + (-J)

instance : Sub DyadicInterval where
  sub := DyadicInterval.sub

def productEndpts : Finset Dyadic :=
  {(I.left * J.left),
  (I.left * J.right),
  (I.right * J.left),
  (I.right * J.right)}

@[simp]
lemma product_endpts_nonempty : (productEndpts I J).Nonempty := by
  unfold productEndpts
  exact insert_nonempty (I.left * J.left) {I.left * J.right, I.right * J.left, I.right * J.right}

def mul : DyadicInterval :=
  let s := productEndpts I J
  have hs := product_endpts_nonempty I J
  ⟨min' s hs, max' s hs, min'_le_max' s hs⟩

instance : Mul DyadicInterval := ⟨DyadicInterval.mul⟩

def powOdd (n : ℕ) (hn : n % 2 = 1) : DyadicInterval :=
  have h : I.left ^ n ≤ I.right ^ n := by
    simp only [le_iff_toRat, toRat_pow]
    rw [Odd.pow_le_pow]
    · rw [← le_iff_toRat]
      exact I.isValid
    · rw [Nat.odd_iff]
      exact hn
  ⟨(I.left ^ n), (I.right ^ n), h⟩

def powEven (n : ℕ) (hn : n % 2 = 0): DyadicInterval :=
  let s : Finset Dyadic := {0, (I.left^n), (I.right^n)}
  have hs : s.Nonempty := insert_nonempty 0 {(I.left^n), (I.right^n)}
  ⟨min' s hs, max' s hs, min'_le_max' s hs⟩

def powExact (n : ℕ) : DyadicInterval :=
  match n with
  | 0 => ⟨1, 1, le_rfl⟩
  | n + 1 =>
    match h: (n + 1) % 2 with
      | 0 => powEven I (n + 1) h
      | 1 => powOdd I (n+1) h
      | n + 2 => by grind only

def pow (I : DyadicInterval) : ℕ → DyadicInterval
| 0     => 1
| (n+1) => (pow I n) * I

instance : Pow DyadicInterval Nat := ⟨DyadicInterval.powExact⟩

@[simp]
lemma left_coe_zero : (0 : DyadicInterval).left = 0 := by rfl

@[simp]
lemma right_coe_zero : (0 : DyadicInterval).right = 0 := by rfl

@[simp]
lemma left_add_eq : (I + J).left = I.left + J.left := by rfl

@[simp]
lemma right_add_eq : (I + J).right = I.right + J.right := by rfl

@[simp]
lemma mul_left_endpt : (I * J).left =
  (productEndpts I J).min' (product_endpts_nonempty I J) := by rfl

@[simp]
lemma mul_right_endpt : (I * J).right =
  (productEndpts I J).max' (product_endpts_nonempty I J) := by rfl
@[simp]
lemma neg_left : (- I).left = -I.right := by rfl

@[simp]
lemma neg_right : (-I).right = -I.left := by rfl

@[simp]
lemma sub_eq_neg_add : I - J = I + (-J) := by rfl

@[simp]
lemma left_sub_eq : (I - J).left = I.left - J.right := by
  simp only [sub_eq_neg_add, left_add_eq, neg_left, Dyadic.sub_eq_add_neg]

@[simp]
lemma right_sub_eq : (I - J).right = I.right - J.left := by
  simp only [sub_eq_neg_add, right_add_eq, neg_right, Dyadic.sub_eq_add_neg]

@[simp]
theorem eq_iff_left_right : I = J ↔ I.left = J.left ∧ I.right = J.right := by
  constructor
  · intro h
    cases I
    cases J
    simp only [mk.injEq] at *
    exact h
  · intro h
    cases I
    cases J
    simp only [mk.injEq] at *
    exact h

@[simp]
theorem mem_iff_le_endpts : ∀ x : ℝ, x ∈ I ↔ I.left.toRat ≤ x ∧ x ≤ I.right.toRat := by intro x; rfl

@[simp]
lemma product_endpts_comm : productEndpts I J = productEndpts J I := by
  simp only [productEndpts, Dyadic.mul_comm]
  grind only [= Set.mem_singleton_iff, = mem_singleton, = insert_eq_of_mem, = mem_insert, cases Or]

-- maybe we won't need these
-- def all_endpts : Finset Dyadic :=
--     {I.left*J.left*K.left, I.left*J.left*K.right, I.left*J.right*K.left, I.left*J.right*K.right,
--     I.right*J.left*K.left, I.right*J.left*K.right, I.right*J.right*K.left, I.right*J.right*K.right}

-- lemma product_endpts_assoc_min :
--   ((I * J).productEndpts K).min' (by simp) = (I.productEndpts (J * K)).min' (by simp) := by
--   have h : ((I * J).productEndpts K).min' (by simp) = (all_endpts I J K).min' (by sorry) :=
--     by sorry
--   have h' : (I.productEndpts (J * K)).min' (by simp) = (all_endpts I J K).min' (by sorry) :=
--     by sorry
--   rw [h, h']

-- lemma product_endpts_assoc_max :
--   ((I * J).productEndpts K).max' (by simp) = (I.productEndpts (J * K)).max' (by simp) := by
--   have h : ((I * J).productEndpts K).max' (by simp) = (all_endpts I J K).max' (by sorry) :=
--     by sorry
--   have h' : (I.productEndpts (J * K)).max' (by simp) = (all_endpts I J K).max' (by sorry) :=
--     by sorry
--   rw [h, h']

@[simp]
lemma product_endpts_zero : productEndpts I 0 = {0} := by
  simp only [productEndpts, left_coe_zero, right_coe_zero]
  simp only [Dyadic.mul_zero, mem_singleton, insert_eq_of_mem]

@[simp]
lemma product_endpts_one : productEndpts I 1 = {I.left, I.right} := by
  have h₁ : left 1 = 1 := by rfl
  have h₂ : right 1 = 1 := by rfl
  simp only [productEndpts, h₁, h₂, Dyadic.mul_one]
  simp only [mem_singleton, insert_eq_of_mem, mem_insert, true_or]

@[simp]
theorem add_comm : I + J = J + I := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_comm, and_self]

@[simp]
theorem add_assoc : (I + J) + K = I + (J + K) := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_assoc, and_self]

@[simp]
theorem zero_add : I + 0 = I := by
  rw [eq_iff_left_right, left_add_eq, right_add_eq]
  constructor
  · rw [left_coe_zero, Dyadic.add_zero]
  · rw [right_coe_zero, Dyadic.add_zero]

@[simp]
theorem add_zero : 0 + I = I := by
  rw [add_comm, zero_add]

@[simp]
theorem mul_comm : I * J = J * I := by
  simp only [eq_iff_left_right, mul_left_endpt, mul_right_endpt, product_endpts_comm, and_self]

@[simp]
theorem mul_assoc : (I * J) * K = I * (J * K) := by sorry
-- Will prove this by sharpness of multiplication later

@[simp]
theorem neg_mul : -I * J = - (I * J) := by
  simp only [eq_iff_left_right]
  constructor
  · simp only [mul_left_endpt, productEndpts, neg_left, mul_right_endpt, neg_right]
    apply Dyadic.neg_min'_neg
    · intro s hs
      simp only [mem_insert, mem_singleton] at *
      grind only [cases Or]
    · intro s hs
      simp only [mem_insert, mem_singleton] at *
      grind only [cases Or]
  · simp only [mul_left_endpt, productEndpts, neg_left, mul_right_endpt, neg_right]
    apply Dyadic.neg_max'_neg
    · intro s hs
      simp only [mem_insert, mem_singleton] at *
      grind only [cases Or]
    · intro s hs
      simp only [mem_insert, mem_singleton] at *
      grind only [cases Or]

-- neg_add_cancel is not true!
-- [-1,1] - [-1,1] = [-2,2]

@[simp]
theorem mul_zero : I * 0 = 0 := by
  simp only [eq_iff_left_right, mul_left_endpt, product_endpts_zero, min'_singleton, left_coe_zero,
    mul_right_endpt, max'_singleton, right_coe_zero, and_self]

@[simp]
theorem zero_mul : 0 * I = 0 := by rw [mul_comm, mul_zero]

@[simp]
theorem mul_one : I * 1 = I := by
  simp only [eq_iff_left_right, mul_left_endpt, product_endpts_one, mul_right_endpt]
  constructor
  · simp only [min'_eq_iff, mem_insert, mem_singleton, true_or, forall_eq_or_imp, le_refl, forall_eq, true_and, I.isValid]
  · simp only [max'_eq_iff, mem_insert, mem_singleton, or_true, forall_eq_or_imp, forall_eq, le_refl, and_true, I.isValid]

@[simp]
theorem one_mul : 1 * I = I := by rw [mul_comm, mul_one]

theorem add_sound : ∀ x ∈ I, ∀ y ∈ J, x + y ∈ (I + J) := by
  intro x hx y hy
  constructor
  · rw [left_add_eq, toRat_add, Rat.cast_add]
    apply add_le_add
    · exact hx.left
    · exact hy.left
  · rw [right_add_eq, toRat_add, Rat.cast_add]
    apply add_le_add
    · exact hx.right
    · exact hy.right

theorem neg_sound : ∀ x ∈ I, -x ∈ -I := by
  intro x hx
  constructor
  · rw [neg_left, toRat_neg, Rat.cast_neg]
    apply neg_le_neg
    exact hx.right
  · rw [neg_right, toRat_neg, Rat.cast_neg]
    apply neg_le_neg
    exact hx.left

theorem sub_sound : ∀ x ∈ I, ∀ y ∈ J, x - y ∈ (I - J) := by
  intro x hx y hy
  constructor
  · rw [left_sub_eq, toRat_sub, Rat.cast_sub]
    apply sub_le_sub
    · exact hx.left
    · exact hy.right
  · rw [right_sub_eq, toRat_sub, Rat.cast_sub]
    apply sub_le_sub
    · exact hx.right
    · exact hy.left

theorem mul_sound : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ (I * J) := by
  intro x hx y hy
  constructor
  · sorry
  · sorry

theorem pow_sound : ∀ x ∈ I, ∀ n : ℕ, x ^ n ∈ (I ^ n) := by sorry

end
end DyadicInterval

def x := (0 : ℝ)
def a := Dyadic.ofOdd (-3) 5 (by ring)
def b := Dyadic.ofOdd (7) 3 (by ring)
def I : DyadicInterval := ⟨a, b, by decide⟩
def J : DyadicInterval := ⟨a, b, by decide⟩
def J' : DyadicInterval := ⟨(a-1), b, by decide⟩
#eval I = J
#eval I = J'
#eval (I + J).left.toRat
#eval (I + J).right.toRat
#eval (I * J).left.toRat
#eval (I * J).right.toRat
#eval (I + 3).left.toRat
