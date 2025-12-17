import Mathlib
open Dyadic Finset
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.unusedVariables false
set_option linter.style.longLine false

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

@[simp]
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

@[simp]
lemma toRat_max {a b : Dyadic} : (max a b).toRat = max a.toRat b.toRat := by
  rcases le_total a b with ha | hb
  · rw [max_eq_right ha, max_eq_right]
    rw [← le_iff_toRat]; exact ha
  · rw [max_eq_left hb, max_eq_left]
    rw [← le_iff_toRat]; exact hb


@[simp]
lemma toRat_min {a b : Dyadic} : (min a b).toRat = min a.toRat b.toRat := by
  rcases le_total a b with ha | hb
  · rw [min_eq_left ha, min_eq_left]
    rw [← le_iff_toRat]; exact ha
  · rw [min_eq_right hb, min_eq_right]
    rw [← le_iff_toRat]; exact hb

end Dyadic

structure DyadicInterval where
  left : Dyadic
  right : Dyadic
  isValid : left ≤ right
  deriving DecidableEq

---------------------------------------------------------------------
namespace DyadicInterval
section
variable (I J K : DyadicInterval)(a : Dyadic)(n : ℕ)


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
  let s : Finset Dyadic := if (I.left ≤ 0 ∧ 0 ≤ I.right) then {0, (I.left^n), (I.right^n)}
                          else {(I.left^n), (I.right^n)}
  have hs : s.Nonempty := by
    unfold s
    split_ifs
    · exact insert_nonempty 0 {(I.left^n), (I.right^n)}
    · exact insert_nonempty (I.left^n) {(I.right^n)}
  ⟨min' s hs, max' s hs, min'_le_max' s hs⟩

def powExact (n : ℕ) : DyadicInterval :=
  match n with
  | 0 => ⟨1, 1, le_rfl⟩
  | n + 1 =>
    match h: (n + 1) % 2 with
      | 0 => powEven I (n + 1) h
      | 1 => powOdd I (n+1) h
      | n + 2 => by grind only

-- def powNonzero (n : ℕ) : DyadicInterval :=
--   let condition := n % 2 = 0 ∧ (I.left ≤ 0 ∧ 0 ≤ I.right)
--   let U := max (I.left^n) (I.right^n)
--   let L' := min (I.left^n) (I.right^n)
--   let L := if condition then 0 else L'
--   have h : L ≤ U := by
--     unfold L condition U
--     split_ifs with h
--     · have h₁ : 0 ≤ I.right^n := by
--         simp only [le_iff_toRat, toRat_pow]
--         have : Even n := Nat.even_iff.mpr h.left
--         apply Even.pow_nonneg this
--       exact le_trans h₁ (le_max_right (I.left ^ n) (I.right ^ n))
--     · unfold L'
--       exact min_le_max
--   ⟨L, U, h⟩

-- def powExact (n : ℕ) : DyadicInterval :=
--   match n with
--   | 0 => ⟨1, 1, le_rfl⟩
--   | n + 1 => powNonzero I (n + 1)

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
theorem mem_iff_le_endpts : ∀ x : ℝ, x ∈ I ↔ I.left.toRat ≤ x ∧ x ≤ I.right.toRat := by intro x; rfl

@[simp]
theorem mem_iff_mem_Icc : ∀ x : ℝ, x ∈ I ↔ x ∈ Set.Icc (I.left.toRat : ℝ) (I.right.toRat : ℝ) := by
  intro x; simp only [mem_iff_le_endpts, Set.mem_Icc]

@[simp]
lemma left_mem : (I.left.toRat : ℝ) ∈ I := by
  simp only [mem_iff_le_endpts, le_refl, Rat.cast_le, true_and, ← le_iff_toRat, I.isValid]

@[simp]
lemma right_mem : (I.right.toRat : ℝ) ∈ I := by
  simp only [mem_iff_le_endpts, Rat.cast_le, le_refl, and_true, ← le_iff_toRat, I.isValid]

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
lemma mul_left_mem_product_endpts : (I * J).left ∈ productEndpts I J := by
  simp only [mul_left_endpt, min'_mem]

@[simp]
lemma mul_right_mem_product_endpts : (I * J).right ∈ productEndpts I J := by
  simp only [mul_right_endpt, max'_mem]


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

lemma mul_left_le_left_mul (y : ℝ) (hy : y ∈ J) : ↑(I * J).left.toRat ≤ ↑I.left.toRat * y := by
  rw [mem_iff_le_endpts] at hy
  rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.left.toRat * J.left.toRat := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, true_or]
    exact le_trans h₁ (mul_le_mul_of_nonneg_left hy.left hl)
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.left.toRat * J.right.toRat := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    apply le_trans h₁ (mul_le_mul_of_nonpos_left hy.right hr)

lemma mul_left_le_right_mul (y : ℝ) (hy : y ∈ J) : ↑(I * J).left.toRat ≤ ↑I.right.toRat * y := by
  rw [mem_iff_le_endpts] at hy
  rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.right.toRat * J.left.toRat := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    exact le_trans h₁ (mul_le_mul_of_nonneg_left hy.left hl)
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.right.toRat * J.right.toRat := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, or_true]
    apply le_trans h₁ (mul_le_mul_of_nonpos_left hy.right hr)

lemma left_mul_le_mul_right (y : ℝ) (hy : y ∈ J) : ↑I.left.toRat * y ≤ ↑(I * J).right.toRat := by
  rw [mem_iff_le_endpts] at hy
  rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
  · have h₁ : I.left.toRat * J.right.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    exact le_trans (mul_le_mul_of_nonneg_left hy.right hl) h₁
  · have h₁ : I.left.toRat * J.left.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, true_or]
    exact le_trans (mul_le_mul_of_nonpos_left hy.left hr) h₁

lemma right_mul_le_mul_right (y : ℝ) (hy : y ∈ J) : ↑I.right.toRat * y ≤ ↑(I * J).right.toRat := by
  rw [mem_iff_le_endpts] at hy
  rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
  · have h₁ : I.right.toRat * J.right.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, or_true]
    exact le_trans (mul_le_mul_of_nonneg_left hy.right hl) h₁
  · have h₁ : I.right.toRat * J.left.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, ← le_iff_toRat]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    exact le_trans (mul_le_mul_of_nonpos_left hy.left hr) h₁

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

-- Soundness of Operations
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
  rw [mem_iff_le_endpts] at hx
  rcases le_total 0 y with hl | hr
  · have h₁ : ↑I.left.toRat * y ≤ x * y ∧ x * y ≤ ↑I.right.toRat * y := by
      constructor
      · apply mul_le_mul_of_nonneg_right hx.left hl
      · apply mul_le_mul_of_nonneg_right hx.right hl
    constructor
    · exact le_trans (mul_left_le_left_mul I J y hy) h₁.left
    · exact le_trans h₁.right (right_mul_le_mul_right I J y hy)
  · have h₁ : x * y ≤ ↑I.left.toRat * y ∧ ↑I.right.toRat * y ≤ x * y := by
      constructor
      · apply mul_le_mul_of_nonpos_right hx.left hr
      · apply mul_le_mul_of_nonpos_right hx.right hr
    constructor
    · exact le_trans (mul_left_le_right_mul I J y hy) h₁.right
    · exact le_trans h₁.left (left_mul_le_mul_right I J y hy)

theorem powOdd_sound (hn : n % 2 = 1) : ∀ x ∈ I, x ^ n ∈ powOdd I n hn := by
  intro x hx
  simp only [mem_iff_le_endpts, powOdd, toRat_pow, Rat.cast_pow]
  rw [← Nat.odd_iff] at hn
  constructor
  · rw [Odd.pow_le_pow hn]
    exact hx.left
  · rw [Odd.pow_le_pow hn]
    exact hx.right

theorem powEven_sound (hn : n % 2 = 0) : ∀ x ∈ I, x ^ n ∈ powEven I n hn := by
  intro x hx
  simp only [mem_iff_le_endpts, powEven]
  rw [← Nat.even_iff] at hn
  split_ifs with h₀
  -- I crosses 0
  · let S : Finset Dyadic := {0, I.left ^ n, I.right ^ n}
    have hS : S.Nonempty := by exact insert_nonempty 0 {I.left ^ n, I.right ^ n}
    let s := S.min' hS
    let s' := S.max' hS
    change s.toRat ≤ x ^ n ∧ x ^ n ≤ s'.toRat
    constructor
    · have h₁ : 0 ≤ x ^ n := by apply Even.pow_nonneg hn
      have h₂ : s.toRat ≤ (0 : ℝ) := by
        norm_cast
        rw [← toRat_zero, ← le_iff_toRat]
        apply min'_le
        simp only [S, mem_insert, mem_singleton, true_or]
      exact le_trans h₂ h₁
    · rcases le_total 0 x with hx' | hx'
      · have h₁ : x ^ n ≤ (I.right ^ n).toRat := by
          rw [toRat_pow, Rat.cast_pow]
          apply pow_le_pow_left₀ hx' hx.right
        have h₂ : (I.right ^ n).toRat ≤ (s'.toRat : ℝ) := by
          norm_cast
          rw [← le_iff_toRat]
          apply le_max'
          simp only [S, mem_insert, mem_singleton, or_true]
        exact le_trans h₁ h₂
      · have h₁ : x ^ n ≤ (I.left ^ n).toRat := by
          rw [toRat_pow, ← Even.neg_pow hn, ← Even.neg_pow hn (I.left.toRat), Rat.cast_pow]
          apply pow_le_pow_left₀
          · grind only
          · simp only [Rat.cast_neg, neg_le_neg_iff, hx.left]
        have h₂ : (I.left ^ n).toRat ≤ (s'.toRat : ℝ) := by
          norm_cast
          rw [← le_iff_toRat]
          apply le_max'
          simp only [S, mem_insert, mem_singleton, true_or, or_true]
        exact le_trans h₁ h₂

  -- I doesn't cross 0
  · rw [mem_iff_le_endpts] at hx
    let S : Finset Dyadic := {I.left ^ n, I.right ^ n}
    let s := S.min' (insert_nonempty (I.left ^ n) {I.right ^ n})
    have hs : s = min (I.left ^ n) (I.right ^ n) := by
      unfold s S
      apply le_antisymm
      · apply le_min
        · apply min'_le; simp only [mem_insert, mem_singleton, true_or]
        · apply min'_le; simp only [mem_insert, mem_singleton, or_true]
      · rcases le_total (I.left ^ n) (I.right ^ n) with h | h
        · rw [min_eq_left h]
          apply le_min'
          simp only [mem_insert, mem_singleton, forall_eq_or_imp, le_refl, forall_eq, true_and, h]
        · rw [min_eq_right h]
          apply le_min'
          simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, le_refl, and_true, h]
    let s' := S.max' (insert_nonempty (I.left ^ n) {I.right ^ n})
    have hs' : s' = max (I.left ^ n) (I.right ^ n) := by
      unfold s' S
      apply le_antisymm
      · apply Finset.max'_le
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro x (rfl | rfl)
        · exact le_max_left _ _
        · exact le_max_right _ _
      · apply max_le
        · apply Finset.le_max'; simp only [mem_insert, mem_singleton, true_or]
        · apply Finset.le_max'; simp only [mem_insert, mem_singleton, or_true]
    change s.toRat ≤ x ^ n ∧ x ^ n ≤ s'.toRat
    simp only [hs, hs', toRat_max, toRat_min, Rat.cast_min, Rat.cast_max, toRat_pow, Rat.cast_pow]
    clear hs hs' S s s'
    simp only [not_and_or, not_le] at h₀
    rcases h₀ with hpos | hneg
    -- 0 ≤ L ≤ x ≤ R
    · have h₁ : (I.left.toRat : ℝ) ^ n ≤ x ^ n := by
        apply pow_le_pow_left₀ _ hx.left
        norm_cast
        rw [← toRat_zero, ← le_iff_toRat]
        grind only
      have h₂ : x ^ n ≤ (I.right.toRat : ℝ) ^ n := by
        apply pow_le_pow_left₀ _ hx.right
        apply le_trans _ hx.left
        norm_cast
        rw [← toRat_zero, ← le_iff_toRat]
        grind only
      constructor
      · exact le_trans (min_le_left _ _) h₁
      · exact le_trans h₂ (le_max_right _ _)
    -- L ≤ x ≤ R ≤ 0
    · have h₁ : (I.right.toRat : ℝ) ^ n ≤ x ^ n := by
        rw [← Even.neg_pow hn, ← Even.neg_pow hn x]
        apply pow_le_pow_left₀
        · norm_cast
          rw [← toRat_zero, ← toRat_neg, ← le_iff_toRat]
          grind only
        · grind only
      have h₂ : x ^ n ≤ (I.left.toRat : ℝ) ^ n := by
        rw [← Even.neg_pow hn, ← Even.neg_pow hn (I.left.toRat : ℝ)]
        apply pow_le_pow_left₀
        · rw [← neg_zero]
          apply neg_le_neg
          apply le_trans hx.right
          norm_cast
          rw [← toRat_zero, ← le_iff_toRat]
          grind only
        · exact neg_le_neg hx.left
      constructor
      · exact le_trans (min_le_right _ _) h₁
      · exact le_trans h₂ (le_max_left _ _)

theorem pow_sound : ∀ x ∈ I, x ^ n ∈ (I ^ n) := by
  intro x hx
  change x ^ n ∈ DyadicInterval.powExact I n
  unfold powExact
  split
  -- n' = 0
  · simp only [pow_zero, mem_iff_le_endpts]
    norm_cast
  -- n' = n + 1
  -- · rename_i n' n
  --   simp only [Nat.succ_eq_add_one, mem_iff_le_endpts, powNonzero]
  --   split_ifs with h₀
  --   -- n + 1 is even and interval crosses zero
  --   · have h_even : Even (n + 1) := Nat.even_iff.mpr h₀.left
  --     constructor
  --     · simp only [toRat_zero, Rat.cast_zero]
  --       apply Even.pow_nonneg h_even
  --     · rw [mem_iff_le_endpts] at hx
  --       rw [toRat_max, Rat.cast_max, le_max_iff, toRat_pow, Rat.cast_pow, toRat_pow, Rat.cast_pow]
  --       rw [← Even.pow_abs h_even, ← Even.pow_abs h_even (I.left.toRat : ℝ),
  --           ← Even.pow_abs h_even (I.right.toRat : ℝ)]
  --       rcases le_total |↑I.left.toRat| |↑I.right.toRat| with h_abs | h_abs'
  --       · right
  --         apply pow_le_pow_left₀ (abs_nonneg x)
  --         rw [abs_le]
  --         constructor
  --         · sorry
  --         · sorry
  --       · left
  --         sorry
  --   -- Either n + 1 is odd or n + 1 is even but I doesn't cross 0
  --   · rw [toRat_max, Rat.cast_max, le_max_iff, toRat_pow, Rat.cast_pow, toRat_pow, Rat.cast_pow]
  --     sorry
  · split
    -- n + 1 is even
    · rename_i n' n hn
      apply powEven_sound I (n + 1) hn x hx
    -- n + 1 is odd
    · rename_i n' n hn
      apply powOdd_sound I (n +1) hn x hx
    -- unreachable
    · grind only

-- Sharpness of Operations
theorem add_sharp : ∀ z ∈ (I + J), ∃ x ∈ I, ∃ y ∈ J, x + y = z := by
  intro z hz
  rw [add_comm] at hz
  simp only [mem_iff_le_endpts, left_add_eq, right_add_eq, toRat_add, Rat.cast_add] at hz
  let x' := max (I.left.toRat : ℝ) (z - J.right.toRat)
  have hx' : x' ∈ I := by
    rw [mem_iff_le_endpts]
    constructor
    · apply le_max_left
    · rcases max_choice (I.left.toRat : ℝ) (z - J.right.toRat) with hl | hr
      · simp only [x', hl, Rat.cast_le, ← le_iff_toRat, I.isValid]
      · simp only [x', hr]
        grind only
  let y' := z - x'
  have hy' : y' ∈ J := by
    unfold y'
    rw [mem_iff_le_endpts] at *
    constructor
    · rw [le_sub_comm]
      rcases max_choice (I.left.toRat : ℝ) (z - J.right.toRat) with hl | hr
      · simp only [x', hl]
        grind only
      · simp only [x', hr, sub_le_sub_iff_left, Rat.cast_le, ← le_iff_toRat, J.isValid]
    · rw [sub_le_comm]
      apply le_max_right
  use x', hx', y', hy'
  simp only [y', add_sub_cancel]

theorem neg_sharp : ∀ z ∈ (-I), ∃ x ∈ I, -x = z := by
-- Although this is fine, consider using IVT
  intro z hz
  simp only [mem_iff_le_endpts, neg_right, neg_left, toRat_neg, Rat.cast_neg] at hz
  use -z
  constructor
  · rw [mem_iff_le_endpts]
    grind only [cases Or]
  · simp only [neg_neg]

theorem sub_sharp : ∀ z ∈ (I - J), ∃ x ∈ I, ∃ y ∈ J, x - y = z := by
  intro z hz
  rw [sub_eq_neg_add] at hz
  rcases add_sharp I (-J) z hz with ⟨x, hx, y', hy', hxy'⟩
  rcases neg_sharp J y' hy' with ⟨y, hy, hyy'⟩
  use x, hx, y, hy
  grind only

lemma productEndpts_image : ∀ z ∈ productEndpts I J, ∃ x ∈ I, ∃ y ∈ J, x * y = z.toRat := by
  intro z hz
  simp [productEndpts] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · use I.left.toRat, left_mem I, J.left.toRat, left_mem J; simp only [toRat_mul, Rat.cast_mul]
  · use I.left.toRat, left_mem I, J.right.toRat, right_mem J; simp only [toRat_mul, Rat.cast_mul]
  · use I.right.toRat, right_mem I, J.left.toRat, left_mem J; simp only [toRat_mul, Rat.cast_mul]
  · use I.right.toRat, right_mem I, J.right.toRat, right_mem J; simp only [toRat_mul, Rat.cast_mul]

theorem mul_sharp : ∀ z ∈ (I * J), ∃ x ∈ I, ∃ y ∈ J, x * y = z := by
  intro z hz
  rw [mem_iff_le_endpts] at hz
  let Domain := Set.Icc (I.left.toRat : ℝ) I.right.toRat ×ˢ Set.Icc (J.left.toRat : ℝ) J.right.toRat
  let Image := (fun (p : ℝ × ℝ) ↦ p.1 * p.2) '' Domain

  have h₁ : IsConnected Domain := by
    apply IsConnected.prod
    · apply isConnected_Icc
      simp only [Rat.cast_le, ← le_iff_toRat, I.isValid]
    · apply isConnected_Icc
      simp only [Rat.cast_le, ← le_iff_toRat, J.isValid]

  have h₂ : IsConnected Image := by
    apply IsConnected.image h₁
    apply Continuous.continuousOn
    exact continuous_mul

  have h₃ : ((I * J).left.toRat : ℝ) ∈ Image := by
    simp only [Image, Set.mem_image, Prod.exists]
    obtain ⟨x, hx, y, hy, hxy⟩ := productEndpts_image I J (I * J).left (mul_left_mem_product_endpts I J)
    use x, y
    constructor
    · simp only [Domain, Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk]
      rw [mem_iff_le_endpts] at hx hy
      grind only
    · exact hxy
  have h₄ : ((I * J).right.toRat : ℝ) ∈ Image := by
    simp only [Image, Set.mem_image, Prod.exists]
    obtain ⟨x, hx, y, hy, hxy⟩ := productEndpts_image I J (I * J).right (mul_right_mem_product_endpts I J)
    use x, y
    constructor
    · simp only [Domain, Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk]
      rw [mem_iff_le_endpts] at hx hy
      grind only
    · exact hxy

  have h : z ∈ Image := by
    apply Set.mem_of_subset_of_mem
    apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
    simp only [Set.mem_Icc, hz, and_self]

  rcases h with ⟨⟨x,y⟩, ⟨hx, hy⟩, h_mem⟩
  use x, hx, y, hy

theorem powOdd_sharp (hn : n % 2 = 1) : ∀ z ∈ (powOdd I n hn), ∃ x ∈ I, x ^ n = z := by
  intro z hz
  dsimp [powOdd] at hz
  simp only [mem_iff_le_endpts, toRat_pow, Rat.cast_pow] at hz
  let Domain := Set.Icc (I.left.toRat : ℝ) I.right.toRat
  let Image := (fun x ↦ x ^ n) '' Domain

  have h₁ : IsConnected Domain := by
    apply isConnected_Icc
    simp only [Rat.cast_le, ← le_iff_toRat, I.isValid]

  have h₂ : IsConnected Image := by
    apply IsConnected.image h₁
    apply Continuous.continuousOn
    apply continuous_pow

  have h₃ : ((I.left.toRat ^ n) : ℝ) ∈ Image := by
    simp only [Image, Set.mem_image]
    use (I.left.toRat : ℝ)
    constructor
    · apply Set.left_mem_Icc.mpr
      simp only [Rat.cast_le, ← le_iff_toRat, I.isValid]
    · simp only

  have h₄ : ((I.right.toRat ^ n) : ℝ) ∈ Image := by
    simp only [Image, Set.mem_image]
    use (I.right.toRat : ℝ)
    constructor
    · apply Set.right_mem_Icc.mpr
      simp only [Rat.cast_le, ← le_iff_toRat, I.isValid]
    · simp only

  have h : z ∈ Image := by
    apply Set.mem_of_subset_of_mem
    apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
    simp only [Set.mem_Icc, hz, and_self]

  rcases h with ⟨x, hx, hx'⟩
  use x, hx, hx'

theorem powEven_sharp (hn : n % 2 = 0) : ∀ z ∈ (powEven I n hn), ∃ x ∈ I, x ^ n = z := by
  intro z hz
  rw [← Nat.even_iff] at hn
  dsimp [powEven] at hz
  let Domain := Set.Icc (I.left.toRat : ℝ) I.right.toRat
  let Image := (fun x ↦ x ^ n) '' Domain
  have h₁ : IsConnected Domain := by
    apply isConnected_Icc
    simp only [Rat.cast_le, ← le_iff_toRat, I.isValid]

  have h₂ : IsConnected Image := by
    apply IsConnected.image h₁
    apply Continuous.continuousOn
    apply continuous_pow

  split_ifs at hz with hI
  -- I crosses 0
  · simp only [mem_iff_le_endpts] at hz
    let S : Finset Dyadic := {0, I.left ^ n, I.right ^ n}
    sorry
  -- I doesn't cross 0
  · simp only [mem_iff_le_endpts] at hz
    sorry

theorem pow_sharp : ∀ z ∈ (I ^ n), ∃ x ∈ I, x ^ n = z := by
  intro z hz
  change z ∈ DyadicInterval.powExact I n at hz
  unfold powExact at hz
  split at hz
  -- n = 0
  · simp only [mem_iff_le_endpts] at hz
    rw [← le_antisymm_iff] at hz
    rw [← hz]
    use I.left.toRat, left_mem I
    norm_cast
  -- n > 0
  · split at hz
    -- (n + 1) is even
    · rename_i n' n hn
      obtain ⟨x, hx⟩ := powEven_sharp I (n + 1) hn z hz
      grind only
    -- (n + 1) is odd
    · rename_i n' n hn
      obtain ⟨x, hx⟩ := powOdd_sharp I (n + 1) hn z hz
      grind only
    -- unreachable
    · grind only

@[simp]
theorem mul_assoc : (I * J) * K = I * (J * K) := by sorry
-- Will prove this by sharpness of multiplication later

-- Distributivity doesn't hold in either direction. Choose counterexamples

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
