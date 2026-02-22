import Mathlib
import DyadicRealm.DyadicIntervals.Basic
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
/-!
# Arithmetic on Dyadic Intervals
This file defines addition, subtraction, multiplication, and exponentiation on dyadic intervals,
and proves their basic properties.

## Main Results
- Addition and Multiplication are commutative and associative.
- Subdistributive laws for multiplication over addition.
- `Soundness` : If x ∈ I and y ∈ J, then x ∘ y ∈ I ∘ J for ∘ ∈ {+, -, *}, similarly for exponentiation.
- `Sharpness` : For any z ∈ I ∘ J, there exist x ∈ I and y ∈ J such that x ∘ y = z for ∘ ∈ {+, -, *},
  similarly for exponentiation.
- `Exactness` : The set of all x ∘ y for x ∈ I and y ∈ J is exactly the interval I ∘ J for ∘ ∈ {+, -, *},
  similarly for exponentiation.
- `Isotonicity` : If I ⊆ A and J ⊆ B, then I ∘ J ⊆ A ∘ B for ∘ ∈ {+, -, *}, similarly for exponentiation.

-/
namespace DyadicInterval
section Addition
open Dyadic DyadicInterval Set
variable (I J K : DyadicInterval){A B : DyadicInterval}(a : Dyadic)(n : ℕ)

def add : DyadicInterval :=
  let l := I.left + J.left
  let r := I.right + J.right
  have h : l ≤ r := add_le_add' I.isValid J.isValid
  ⟨l, r, h⟩

instance : Add DyadicInterval := ⟨DyadicInterval.add⟩

/-- The left endpoint of the sum of two dyadic intervals is the sum of their left endpoints -/
lemma left_add_eq : (I + J).left = I.left + J.left := by rfl

/-- The right endpoint of the sum of two dyadic intervals is the sum of their right endpoints -/
lemma right_add_eq : (I + J).right = I.right + J.right := by rfl

theorem add_comm : I + J = J + I := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_comm, and_self]

theorem add_assoc : (I + J) + K = I + (J + K) := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_assoc, and_self]

theorem add_zero : I + 0 = I := by
  rw [eq_iff_left_right, left_add_eq, right_add_eq]
  constructor
  · rw [left_coe_zero, Dyadic.add_zero]
  · rw [right_coe_zero, Dyadic.add_zero]

theorem zero_add : 0 + I = I := by rw [add_comm, add_zero]

theorem add_right_cancel : I + J = K + J → I = K := by
  intro h; simp only [add_comm, eq_iff_left_right, left_add_eq, right_add_eq] at *
  grind only

theorem add_left_cancel : I + J = I + K → J = K := by grind only [add_comm, add_right_cancel]

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
      · simp only [x', hl, I.isValid']
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
      · simp only [x', hr, sub_le_sub_iff_left, J.isValid']
    · rw [sub_le_comm]
      apply le_max_right
  use x', hx', y', hy'
  simp only [y', add_sub_cancel]

theorem add_exact : (I + J : Set ℝ) = image2 (· + ·) I J := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := add_sharp I J z hz
    exact mem_image2_of_mem hx hy
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact add_sound I J x hx y hy

theorem add_isotonic (hI : I ⊆ A) (hJ : J ⊆ B) : I + J ⊆ A + B := by
  simp only [subset_iff, add_exact, image2_add]
  exact add_subset_add ((subset_iff I A).mp hI) ((subset_iff J B).mp hJ)

end Addition

section Subtraction
open Dyadic DyadicInterval Set
variable (I J K : DyadicInterval){A B : DyadicInterval}(a : Dyadic)(n : ℕ)

def neg (I : DyadicInterval) : DyadicInterval :=
  have h : -I.right ≤ -I.left := by
     simp only [← toRat_le_toRat_iff, toRat_neg, neg_le_neg_iff, I.isValid_toRat]
  ⟨-I.right, -I.left, h⟩

instance : Neg DyadicInterval := ⟨DyadicInterval.neg⟩

lemma neg_left : (- I).left = -I.right := by rfl

lemma neg_right : (-I).right = -I.left := by rfl

theorem neg_neg : - (-I) = I := by
  apply ext; simp only [toSet, neg_left, neg_right, _root_.neg_neg]

theorem neg_add_rev : -(I + J) = -J + -I := by
  simp only [add_comm, eq_iff_left_right, neg_left, right_add_eq, left_add_eq, neg_right]
  grind only

def sub : DyadicInterval := I + (-J)

instance : Sub DyadicInterval where sub := DyadicInterval.sub

lemma sub_eq_neg_add : I - J = I + (-J) := by rfl

/-- The left endpoint of the difference of two dyadic intervals is the difference of their left and right endpoints respectively -/
lemma left_sub : (I - J).left = I.left - J.right := by
  simp only [sub_eq_neg_add, left_add_eq, neg_left, Dyadic.sub_eq_add_neg]

/-- The right endpoint of the difference of two dyadic intervals is the difference of their right and left endpoints respectively -/
lemma right_sub : (I - J).right = I.right - J.left := by
  simp only [sub_eq_neg_add, right_add_eq, neg_right, Dyadic.sub_eq_add_neg]

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
  · rw [left_sub, toRat_sub, Rat.cast_sub]
    apply sub_le_sub
    · exact hx.left
    · exact hy.right
  · rw [right_sub, toRat_sub, Rat.cast_sub]
    apply sub_le_sub
    · exact hx.right
    · exact hy.left

theorem neg_sharp : ∀ z ∈ (-I), ∃ x ∈ I, -x = z := by
-- Although this is fine, consider using IVT
  intro z hz
  simp only [mem_iff_le_endpts, neg_right, neg_left, toRat_neg, Rat.cast_neg] at hz
  use -z
  constructor
  · rw [mem_iff_le_endpts]
    grind only [cases Or]
  · simp only [_root_.neg_neg]

theorem sub_sharp : ∀ z ∈ (I - J), ∃ x ∈ I, ∃ y ∈ J, x - y = z := by
  intro z hz
  rw [sub_eq_neg_add] at hz
  rcases add_sharp I (-J) z hz with ⟨x, hx, y', hy', hxy'⟩
  rcases neg_sharp J y' hy' with ⟨y, hy, hyy'⟩
  use x, hx, y, hy
  grind only

theorem neg_exact : ↑(-I) = Set.image Neg.neg (I : Set ℝ) := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := neg_sharp I z hz
    exact mem_image_of_mem _ hx
  · rintro _ ⟨x, hx, rfl⟩
    exact neg_sound I x hx

theorem sub_exact : (I - J : Set ℝ) = image2 (· - ·) I J := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := sub_sharp I J z hz
    exact mem_image2_of_mem hx hy
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact sub_sound I J x hx y hy

theorem neg_isotonic (hI : I ⊆ A) : -I ⊆ - A := by
  simp only [subset_iff, neg_exact, image_neg_eq_neg, neg_subset_neg]
  rw [← subset_iff]; exact hI

theorem sub_isotonic (hI : I ⊆ A) (hJ : J ⊆ B) : I - J ⊆ A - B := by
  simp only [subset_iff, sub_exact, image2_sub]
  exact sub_subset_sub ((subset_iff I A).mp hI) ((subset_iff J B).mp hJ)

end Subtraction

section ScalarMultiplication
open Dyadic DyadicInterval

def nsmul (n : ℕ) (I : DyadicInterval) : DyadicInterval :=
  have h : n * I.left ≤ n * I.right := by
    induction n with
    | zero => grind only
    | succ m ih => grind only [Dyadic.add_mul, I.isValid]
  ⟨n * I.left, n * I.right, h⟩

def zsmul (z : ℤ) (I : DyadicInterval) : DyadicInterval :=
  match z with
  | Int.ofNat n => nsmul n I
  | Int.negSucc n => - (nsmul (n + 1) I)

end ScalarMultiplication

section Multiplication
open Dyadic DyadicInterval
variable (I J K : DyadicInterval){A B : DyadicInterval}(a : Dyadic)(n : ℕ)

section Part1
open Finset

/-- The finset of products of the endpoints of two dyadic intervals; multiplication is defined using this -/
def productEndpts : Finset Dyadic :=
  {(I.left * J.left),
  (I.left * J.right),
  (I.right * J.left),
  (I.right * J.right)}
 lemma product_endpts_nonempty : (productEndpts I J).Nonempty := by
  grind only [productEndpts, insert_nonempty]

lemma product_endpts_comm : productEndpts I J = productEndpts J I := by
  simp only [productEndpts, Dyadic.mul_comm]
  grind only [= Set.mem_singleton_iff, = mem_singleton, = insert_eq_of_mem, = mem_insert, cases Or]

/-- Multiplication is defined by taking the minimum and maximum of the products of the endpoints -/
def mul : DyadicInterval :=
  let s := productEndpts I J
  have hs := product_endpts_nonempty I J
  ⟨min' s hs, max' s hs, min'_le_max' s hs⟩

instance : Mul DyadicInterval := ⟨DyadicInterval.mul⟩

lemma mul_left_endpt : (I * J).left =
  (productEndpts I J).min' (product_endpts_nonempty I J) := by rfl

lemma mul_right_endpt : (I * J).right =
  (productEndpts I J).max' (product_endpts_nonempty I J) := by rfl
 lemma mul_left_mem_product_endpts : (I * J).left ∈ productEndpts I J := by
  simp only [mul_left_endpt, min'_mem]
 lemma mul_right_mem_product_endpts : (I * J).right ∈ productEndpts I J := by
  simp only [mul_right_endpt, max'_mem]

lemma mul_left_le_left_mul' (y : ℝ) (hy : y ∈ J) : ↑(I * J).left.toRat ≤ ↑I.left.toRat * y := by
  rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.left.toRat * J.left.toRat := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, true_or]
    exact le_trans h₁ (mul_le_mul_of_nonneg_left hy.left hl)
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.left.toRat * J.right.toRat := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    apply le_trans h₁ (mul_le_mul_of_nonpos_left hy.right hr)

lemma mul_left_le_right_mul' (y : ℝ) (hy : y ∈ J) : ↑(I * J).left.toRat ≤ ↑I.right.toRat * y := by
  rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.right.toRat * J.left.toRat := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    exact le_trans h₁ (mul_le_mul_of_nonneg_left hy.left hl)
  · have h₁ : ((I * J).left.toRat : ℝ)  ≤ I.right.toRat * J.right.toRat := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply min'_le
      simp only [productEndpts, mem_insert, mem_singleton, or_true]
    apply le_trans h₁ (mul_le_mul_of_nonpos_left hy.right hr)

lemma left_mul_le_mul_right' (y : ℝ) (hy : y ∈ J) : ↑I.left.toRat * y ≤ ↑(I * J).right.toRat := by
  rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
  · have h₁ : I.left.toRat * J.right.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    exact le_trans (mul_le_mul_of_nonneg_left hy.right hl) h₁
  · have h₁ : I.left.toRat * J.left.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, true_or]
    exact le_trans (mul_le_mul_of_nonpos_left hy.left hr) h₁

lemma right_mul_le_mul_right' (y : ℝ) (hy : y ∈ J) : ↑I.right.toRat * y ≤ ↑(I * J).right.toRat := by
  rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
  · have h₁ : I.right.toRat * J.right.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, or_true]
    exact le_trans (mul_le_mul_of_nonneg_left hy.right hl) h₁
  · have h₁ : I.right.toRat * J.left.toRat ≤ ((I * J).right.toRat : ℝ) := by
      norm_cast
      rw [← toRat_mul, toRat_le_toRat_iff]
      apply le_max'
      simp only [productEndpts, mem_insert, mem_singleton, true_or, or_true]
    exact le_trans (mul_le_mul_of_nonpos_left hy.left hr) h₁

lemma product_endpts_zero : productEndpts I 0 = {0} := by
  simp only [productEndpts, left_coe_zero, right_coe_zero]
  simp only [Dyadic.mul_zero, mem_singleton, insert_eq_of_mem]

lemma product_endpts_one : productEndpts I 1 = {I.left, I.right} := by
  have h₁ : left 1 = 1 := by rfl
  have h₂ : right 1 = 1 := by rfl
  simp only [productEndpts, h₁, h₂, Dyadic.mul_one]
  simp only [mem_singleton, insert_eq_of_mem, mem_insert, true_or]

theorem mul_comm : I * J = J * I := by
  simp only [eq_iff_left_right, mul_left_endpt, mul_right_endpt, product_endpts_comm, and_self]

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

theorem mul_zero : I * 0 = 0 := by
  simp only [eq_iff_left_right, mul_left_endpt, product_endpts_zero, min'_singleton, left_coe_zero,
    mul_right_endpt, max'_singleton, right_coe_zero, and_self]

theorem zero_mul : 0 * I = 0 := by rw [mul_comm, mul_zero]

theorem mul_one : I * 1 = I := by
  simp only [eq_iff_left_right, mul_left_endpt, product_endpts_one, mul_right_endpt]
  constructor
  · simp only [min'_eq_iff, mem_insert, mem_singleton, true_or, forall_eq_or_imp, le_refl, forall_eq, true_and, I.isValid]
  · simp only [max'_eq_iff, mem_insert, mem_singleton, or_true, forall_eq_or_imp, forall_eq, le_refl, and_true, I.isValid]

theorem one_mul : 1 * I = I := by rw [mul_comm, mul_one]

theorem mul_sound : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ (I * J) := by
  intro x hx y hy
  rw [mem_iff_le_endpts] at hx
  rcases le_total 0 y with hl | hr
  · have h₁ : ↑I.left.toRat * y ≤ x * y ∧ x * y ≤ ↑I.right.toRat * y := by
      constructor
      · apply mul_le_mul_of_nonneg_right hx.left hl
      · apply mul_le_mul_of_nonneg_right hx.right hl
    constructor
    · exact le_trans (mul_left_le_left_mul' I J y hy) h₁.left
    · exact le_trans h₁.right (right_mul_le_mul_right' I J y hy)
  · have h₁ : x * y ≤ ↑I.left.toRat * y ∧ ↑I.right.toRat * y ≤ x * y := by
      constructor
      · apply mul_le_mul_of_nonpos_right hx.left hr
      · apply mul_le_mul_of_nonpos_right hx.right hr
    constructor
    · exact le_trans (mul_left_le_right_mul' I J y hy) h₁.right
    · exact le_trans h₁.left (left_mul_le_mul_right' I J y hy)

lemma productEndpts_image : ∀ z ∈ productEndpts I J, ∃ x ∈ I, ∃ y ∈ J, x * y = z.toRat := by
  intro z hz
  simp only [productEndpts, mem_insert, mem_singleton] at hz
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
      exact I.isValid'
    · apply isConnected_Icc
      exact J.isValid'
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
    · apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
    · simp only [Set.mem_Icc, hz, and_self]
  rcases h with ⟨⟨x,y⟩, ⟨hx, hy⟩, h_mem⟩
  use x, hx, y, hy
end Part1
section Part2
open Set
theorem mul_exact : (I * J : Set ℝ) = image2 (· * ·) I J := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mul_sharp I J z hz
    exact mem_image2_of_mem hx hy
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_sound I J x hx y hy

theorem mul_assoc : (I * J) * K = I * (J * K) := by
  ext z; simp only [mul_exact, image2_mul, mem_mul]; grind only

theorem left_subdistrib : I * (J + K) ⊆ I * J + I * K := by
  rw [subset_iff]
  intro z hz
  simp only [toSet, ← mem_iff_mem_Icc] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mul_sharp I (J + K) z hz
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := add_sharp J K y hy
  rw [add_exact, image2_add, _root_.mul_add]
  exact add_mem_add (mul_sound I J x hx y₁ hy₁) (mul_sound I K x hx y₂ hy₂)

theorem right_subdistrib : (J + K) * I ⊆ J * I + K * I := by
 rw [mul_comm (J + K) I, mul_comm J I, mul_comm K I]
 exact left_subdistrib I J K

theorem mul_isotonic (hI : I ⊆ A) (hJ : J ⊆ B) : I * J ⊆ A * B := by
  simp only [subset_iff, mul_exact, image2_mul]
  exact mul_subset_mul ((subset_iff I A).mp hI) ((subset_iff J B).mp hJ)

end Part2
end Multiplication

section NatPower
open Dyadic DyadicInterval Set
variable (I J K : DyadicInterval){A B : DyadicInterval}(a : Dyadic)(n : ℕ)

/-- For odd `n`, the exponentiation fuction is monotonic, so `I^n` is simply `[L^n, R^n]` -/
def powOdd (n : ℕ) (hn : n % 2 = 1) : DyadicInterval :=
  have h : I.left ^ n ≤ I.right ^ n := by
    simp only [← toRat_le_toRat_iff, toRat_pow]
    rw [Odd.pow_le_pow]
    · exact I.isValid_toRat
    · rw [Nat.odd_iff]
      exact hn
  ⟨(I.left ^ n), (I.right ^ n), h⟩

/-- For even `n`, the exponentiation function is not monotonic. If the interval crosses 0, we truncate at 0 for sharpness -/
def powEven (n : ℕ) (hn : n % 2 = 0) : DyadicInterval :=
  let r := max (I.left ^ n) (I.right ^ n)
  let l := min (I.left ^ n) (I.right ^ n)
  let l' := if I.left ≤ 0 ∧ 0 ≤ I.right then 0 else l
  have h : l' ≤ r := by
    rw [← Nat.even_iff] at hn
    unfold l' r l
    split_ifs
    · apply le_max_of_le_left
      rw [← toRat_le_toRat_iff, toRat_zero, toRat_pow]
      apply Even.pow_nonneg hn
    · apply min_le_max
  ⟨l', r, h⟩

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
  · constructor
    · rw [toRat_zero, Rat.cast_zero]
      apply Even.pow_nonneg hn
    · rcases le_total 0 x with hx' | hx'
      · rw [toRat_max, Rat.cast_max]
        apply le_max_of_le_right
        rw [toRat_pow, Rat.cast_pow]
        apply pow_le_pow_left₀ hx' hx.right
      · rw [toRat_max, Rat.cast_max]
        apply le_max_of_le_left
        rw [toRat_pow, ← Even.neg_pow hn,← Even.neg_pow hn (I.left.toRat), Rat.cast_pow]
        apply pow_le_pow_left₀
        · grind only
        · simp only [Rat.cast_neg, neg_le_neg_iff, hx.left]
  -- I doesn't cross 0
  · simp only [not_and_or, not_le] at h₀
    rcases h₀ with hpos | hneg
    -- 0 ≤ L ≤ x ≤ R
    · simp only [toRat_min, Rat.cast_min, toRat_max, Rat.cast_max]
      have h₁ : ((I.left ^ n).toRat : ℝ) ≤ x ^ n := by
        rw [toRat_pow, Rat.cast_pow]
        apply pow_le_pow_left₀ _ hx.left
        norm_cast
        rw [← toRat_zero, toRat_le_toRat_iff]
        grind only
      have h₂ : x ^ n ≤ ((I.right ^ n).toRat : ℝ) := by
        rw [toRat_pow, Rat.cast_pow]
        apply pow_le_pow_left₀ _ hx.right
        apply le_trans _ hx.left
        norm_cast
        rw [← toRat_zero, toRat_le_toRat_iff]
        grind only
      constructor
      · exact le_trans (min_le_left _ _) h₁
      · exact le_trans h₂ (le_max_right _ _)
    -- L ≤ x ≤ R ≤ 0
    · simp only [toRat_min, Rat.cast_min, toRat_max, Rat.cast_max]
      have h₁ : ((I.right ^ n).toRat : ℝ) ≤ x ^ n := by
        rw [toRat_pow, Rat.cast_pow]
        rw [← Even.neg_pow hn, ← Even.neg_pow hn x]
        apply pow_le_pow_left₀
        · norm_cast
          rw [← toRat_zero, ← toRat_neg, toRat_le_toRat_iff]
          grind only
        · rw [mem_iff_le_endpts] at hx
          grind only
      have h₂ : x ^ n ≤ ((I.left ^ n).toRat : ℝ) := by
        rw [toRat_pow, Rat.cast_pow]
        rw [← Even.neg_pow hn, ← Even.neg_pow hn (I.left.toRat : ℝ)]
        apply pow_le_pow_left₀
        · rw [← neg_zero]
          apply neg_le_neg
          apply le_trans hx.right
          norm_cast
          rw [← toRat_zero, toRat_le_toRat_iff]
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
  · split
    -- n + 1 is even
    · rename_i n' n hn
      apply powEven_sound I (n + 1) hn x hx
    -- n + 1 is odd
    · rename_i n' n hn
      apply powOdd_sound I (n +1) hn x hx
    -- unreachable
    · grind only

theorem powOdd_sharp (hn : n % 2 = 1) : ∀ z ∈ (powOdd I n hn), ∃ x ∈ I, x ^ n = z := by
  intro z hz
  dsimp [powOdd] at hz
  simp only [mem_iff_le_endpts, toRat_pow, Rat.cast_pow] at hz
  let Domain := Set.Icc (I.left.toRat : ℝ) I.right.toRat
  let Image := (fun x ↦ x ^ n) '' Domain
  have h₁ : IsConnected Domain := by
    apply isConnected_Icc
    simp only [I.isValid']
  have h₂ : IsConnected Image := by
    apply IsConnected.image h₁
    apply Continuous.continuousOn
    apply continuous_pow
  have h₃ : ((I.left.toRat ^ n) : ℝ) ∈ Image := by
    simp only [Image, Set.mem_image]
    use (I.left.toRat : ℝ)
    constructor
    · apply Set.left_mem_Icc.mpr
      simp only [I.isValid']
    · simp only
  have h₄ : ((I.right.toRat ^ n) : ℝ) ∈ Image := by
    simp only [Image, Set.mem_image]
    use (I.right.toRat : ℝ)
    constructor
    · apply Set.right_mem_Icc.mpr
      simp only [I.isValid']
    · simp only
  have h : z ∈ Image := by
    apply Set.mem_of_subset_of_mem
    · apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
    · simp only [Set.mem_Icc, hz, and_self]
  rcases h with ⟨x, hx, hx'⟩
  use x, hx, hx'

theorem powEven_sharp (hn : n % 2 = 0) (hn' : n ≠ 0) : ∀ z ∈ (powEven I n hn), ∃ x ∈ I, x ^ n = z := by
  intro z hz
  rw [← Nat.even_iff] at hn
  dsimp [powEven] at hz
  let Domain := Set.Icc (I.left.toRat : ℝ) I.right.toRat
  let Image := (fun x ↦ x ^ n) '' Domain
  have h₁ : IsConnected Domain := by
    apply isConnected_Icc
    simp only [I.isValid']
  have h₂ : IsConnected Image := by
    apply IsConnected.image h₁
    apply Continuous.continuousOn
    apply continuous_pow
  have h₄ : max ((I.left.toRat ^ n) : ℝ) ((I.right.toRat ^ n) : ℝ) ∈ Image := by
    simp only [Image, Set.mem_image]
    rcases le_total ((I.left.toRat : ℝ)^n) ((I.right.toRat : ℝ)^n) with h | h
    · rw [max_eq_right h]
      use I.right.toRat
      constructor
      · simp only [Domain, Set.mem_Icc, Rat.cast_le, le_refl, and_true]
        rw  [toRat_le_toRat_iff]
        exact I.isValid
      · rfl
    · rw [max_eq_left h]
      use I.left.toRat
      constructor
      · simp only [Domain, Set.mem_Icc, le_refl, true_and, I.isValid']
      · rfl
  split_ifs at hz with hI
  -- I crosses 0
  · simp only [mem_iff_le_endpts, toRat_zero, Rat.cast_zero,
      toRat_max, Rat.cast_max, toRat_pow, Rat.cast_pow] at hz
    have h₃ : 0 ∈ Image := by
      simp only [Image, Set.mem_image]
      use 0
      constructor
      · simp only [Domain, Set.mem_Icc]
        norm_cast
        rw [← toRat_zero, toRat_le_toRat_iff, toRat_le_toRat_iff]
        exact hI
      · simp only [pow_eq_zero_iff', ne_eq, true_and]
        exact hn'
    have h : z ∈ Image := by
      apply Set.mem_of_subset_of_mem
      · apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
      · simp only [Set.mem_Icc, hz, and_self]
    rcases h with ⟨x, hx, hx'⟩
    use x, hx, hx'
  -- I doesn't cross 0
  · simp only [mem_iff_le_endpts, toRat_min, Rat.cast_min,
      toRat_max, Rat.cast_max, toRat_pow, Rat.cast_pow] at hz
    have h₃ : min ((I.left.toRat ^ n) : ℝ) ((I.right.toRat ^ n) : ℝ) ∈ Image := by
      simp only [Image, Set.mem_image]
      rcases le_total ((I.left.toRat : ℝ)^n) ((I.right.toRat : ℝ)^n) with h | h
      · rw [min_eq_left h]
        use I.left.toRat
        constructor
        · simp only [Domain, Set.mem_Icc, le_refl, true_and, I.isValid']
        · rfl
      · rw [min_eq_right h]
        use I.right.toRat
        constructor
        · simp only [Domain, Set.mem_Icc, le_refl, and_true, I.isValid']
        · rfl
    have h : z ∈ Image := by
      apply Set.mem_of_subset_of_mem
      · apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
      · simp only [Set.mem_Icc, hz, and_self]
    rcases h with ⟨x, hx, hx'⟩
    use x, hx, hx'

#check Rat.mkRat_one 1
theorem pow_sharp : ∀ z ∈ (I ^ n), ∃ x ∈ I, x ^ n = z := by
  intro z hz
  change z ∈ DyadicInterval.powExact I n at hz
  unfold powExact at hz
  split at hz
  -- n = 0
  · simp only [mem_iff_le_endpts, ← le_antisymm_iff] at hz
    rw [← hz]
    use I.left.toRat, left_mem I
    rw [pow_zero]; norm_cast
  -- n > 0
  · split at hz
    -- (n + 1) is even
    · rename_i n' n hn
      have hn' : n + 1 ≠ 0 := by grind only
      obtain ⟨x, hx⟩ := powEven_sharp I (n + 1) hn hn' z hz
      grind only
    -- (n + 1) is odd
    · rename_i n' n hn
      obtain ⟨x, hx⟩ := powOdd_sharp I (n + 1) hn z hz
      grind only
    -- unreachable
    · grind only

theorem pow_exact : ↑(I^n) = (fun x ↦ x ^ n) '' (I : Set ℝ) := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := pow_sharp I n z hz
    exact mem_image_of_mem _ hx
  · rintro _ ⟨x, hx, rfl⟩
    exact pow_sound I n x hx

theorem pow_isotonic (hI : I ⊆ A) : I ^ n ⊆ A ^ n := by
  simp only [subset_iff, pow_exact]
  apply image_mono
  exact (subset_iff I A).mp hI

end NatPower

section typeclass_instances
open Dyadic

instance : AddCommMonoid DyadicInterval where
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmul
  nsmul_zero := by intro I; simp only [nsmul]; norm_cast
  nsmul_succ := by
    intro n I
    simp only [nsmul, add_comm, eq_iff_left_right, left_add_eq, right_add_eq]
    grind only [Dyadic.add_mul]

instance : InvolutiveNeg DyadicInterval := ⟨neg_neg⟩

instance : SubNegMonoid DyadicInterval where
  zsmul := zsmul
  zsmul_zero' := by intro I; simp only [zsmul, nsmul]; norm_cast
  zsmul_succ' := by
    intro n I
    simp only [zsmul, nsmul, add_comm, eq_iff_left_right, left_add_eq, right_add_eq]
    grind only [Dyadic.add_mul]
  zsmul_neg' := by intro n I; simp only [zsmul]

instance : SubtractionCommMonoid DyadicInterval where
  neg_add_rev := neg_add_rev
  neg_eq_of_add := by
    intro I J h
    simp only [eq_iff_left_right, left_add_eq, left_coe_zero, right_add_eq, right_coe_zero,
      neg_left, neg_right, toRat_eq, toRat_neg, add_eq_zero_iff_neg_eq] at *
    simp only [← toRat_neg, ← toRat_eq] at *
    -- simp only [h, eq_comm, and_self]    ⊢ J.left = J.right
    grind only [I.isValid, J.isValid]

instance : AddLeftCancelSemigroup DyadicInterval where
 add_left_cancel := add_left_cancel

instance : AddRightCancelSemigroup DyadicInterval where
  add_right_cancel := by
    intro J; simp only [IsAddRightRegular, Function.Injective]
    intro I K; grind only [add_right_cancel]

instance : CommSemigroup DyadicInterval where
  mul_comm := mul_comm
  mul_assoc := mul_assoc

instance : MulOneClass DyadicInterval where
  one_mul := one_mul
  mul_one := mul_one

end typeclass_instances
end DyadicInterval

open DyadicInterval
def I := ofRatWithPrec 1 ((3: ℚ)/9)
def J := ofRatWithPrec 4 ((4 : ℚ)/7)
#eval I - J
#eval (I - J).abs
