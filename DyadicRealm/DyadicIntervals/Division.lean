import Mathlib
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Division of Dyadic Intervals
Division by a dyadic interval is implemented as `divWithPrec` which takes a precision parameter. It computes the four possible quotient endpoints as rationals, then rounds down the minimum and rounds up the maximum to form a dyadic interval that contains all possible quotients.

## Main Definitions
- `quotientEndpoints I J` : The set of four possible rational endpoints when dividing interval `I` by interval `J`.
- `divWithPrec prec I J` : The dyadic interval that contains all possible quotients of elements from `I` divided by elements from `J`, computed with the specified precision.

## Main Theorems

- `div_sound` : For any `x ∈ I` and `y ∈ J`, the quotient `x / y` lies within the interval `divWithPrec prec I J`.
- `div_isotonic` : If `I ⊆ A` and `J ⊆ B`, then `divWithPrec prec I J ⊆ divWithPrec prec A B`.
-/

section Division
open Dyadic DyadicInterval Finset
variable (I J K : DyadicInterval){A B : DyadicInterval}
-- Dyadic Rationals are not closed under division. So we work around it...

def quotientEndpoints : Finset ℚ :=
  { (I.left.toRat / J.left.toRat),
    (I.left.toRat / J.right.toRat),
    (I.right.toRat / J.left.toRat),
    (I.right.toRat / J.right.toRat)}

lemma quotient_endpoints_nonempty : (quotientEndpoints I J).Nonempty := by
  grind only [quotientEndpoints, insert_nonempty]

def divWithPrec (prec : ℤ) (I J : DyadicInterval): DyadicInterval :=
  if HasZero J then 0 else
  let s := quotientEndpoints I J
  have hs := quotient_endpoints_nonempty I J
  -- Rounding down the left endpoint
  let l := (min' s hs).toDyadic prec
  -- Rounding up the right endpoint
  let r := (max' s hs).toDyadic prec + Dyadic.ofIntWithPrec 1 prec
  have h : l ≤ r := by
    simp only [l, r, le_iff_toRat]
    apply le_trans Rat.toRat_toDyadic_le
    exact le_trans (min'_le_max' s hs) (le_of_lt Rat.lt_toRat_toDyadic_add)
  ⟨l, r, h⟩

variable [ZeroFree J] [ZeroFree B] (prec : ℤ)

lemma div_left_le_left_div' (hpos : 0 < J)(y : ℝ) (hy : y ∈ J) :
  ↑(divWithPrec prec I J).left.toRat ≤ ↑I.left.toRat / y := by
    rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
    · have h₀ : ↑I.left.toRat / ↑J.right.toRat ≤ ↑I.left.toRat / y := by
        apply div_le_div_of_nonneg_left hl _ hy.right
        exact pos_of_mem_pos J hpos y hy
      apply le_trans _ h₀
      norm_cast; simp only [divWithPrec]
      split_ifs with h
      · exfalso; grind only [haszero_iff_not_zerofree]
      · let l := (quotientEndpoints I J).min' (quotient_endpoints_nonempty I J)
        have h₁ : l ≤ I.left.toRat / J.right.toRat := by
          simp only [l]; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        apply le_trans _ h₁
        simp only [l]; exact Rat.toRat_toDyadic_le

    · have h₀ : (I.left.toRat : ℝ) / J.left.toRat ≤ ↑I.left.toRat / y := by
        rw [← (neg_neg I.left.toRat), Rat.cast_neg, neg_div, neg_div, neg_le_neg_iff]
        apply div_le_div_of_nonneg_left _ _ hy.left
        · simp only [Rat.cast_neg, Left.nonneg_neg_iff, hr]
        · norm_cast; rw [← toRat_zero, ← lt_iff_toRat]
          rw [lt_iff, right_coe_zero] at hpos; exact hpos
      apply le_trans _ h₀
      norm_cast; simp only [divWithPrec]
      · split_ifs with h
        · exfalso; grind only [haszero_iff_not_zerofree]
        · simp only
          let l := (quotientEndpoints I J).min' (quotient_endpoints_nonempty I J)
          have h₁ : l ≤ I.left.toRat / J.left.toRat := by
            simp only [l]; apply min'_le
            simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
          apply le_trans _ h₁
          simp only [l]; exact Rat.toRat_toDyadic_le

lemma right_div_le_div_right' (hpos : 0 < J) (y : ℝ) (hy : y ∈ J):
  ↑I.right.toRat / y ≤ ↑(divWithPrec prec I J).right.toRat := by
    rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
    · have h₀ : ↑I.right.toRat / y ≤ (I.right.toRat : ℝ) / J.left.toRat := by
        apply div_le_div_of_nonneg_left hl _ hy.left
        apply pos_of_mem_pos J hpos _ (left_mem J)
      apply le_trans h₀
      norm_cast; simp only [divWithPrec]
      split_ifs with h
      · exfalso; grind only [haszero_iff_not_zerofree]
      · let r := (quotientEndpoints I J).max' (quotient_endpoints_nonempty I J)
        have h₁ : I.right.toRat / J.left.toRat ≤ r := by
          simp only [r]; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        apply le_trans h₁
        simp only [r]; exact (le_of_lt Rat.lt_toRat_toDyadic_add)

    · have h₀ : ↑I.right.toRat / y ≤ (I.right.toRat : ℝ) / J.right.toRat := by
        rw [← (neg_neg I.right.toRat), Rat.cast_neg, neg_div, neg_div, neg_le_neg_iff]
        apply div_le_div_of_nonneg_left _ (pos_of_mem_pos J hpos y hy) hy.right
        simp only [Rat.cast_neg, Left.nonneg_neg_iff, hr]
      apply le_trans h₀
      norm_cast; simp only [divWithPrec]
      split_ifs with h
      · exfalso; grind only [haszero_iff_not_zerofree]
      · let r := (quotientEndpoints I J).max' (quotient_endpoints_nonempty I J)
        have h₁ : I.right.toRat / J.right.toRat ≤ r := by
          simp only [r]; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]
        apply le_trans h₁
        simp only [r]; exact (le_of_lt Rat.lt_toRat_toDyadic_add)

lemma div_left_le_right_div' (hneg : J < 0) (y : ℝ) (hy : y ∈ J):
  ↑(divWithPrec prec I J).left.toRat ≤ ↑I.right.toRat / y := by
    rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
    · have h₀ : ↑I.right.toRat / ↑J.right.toRat ≤ ↑I.right.toRat / y := by
        rw [← (neg_neg J.right.toRat), ← (neg_neg y), Rat.cast_neg, div_neg, div_neg, neg_le_neg_iff]
        apply div_le_div_of_nonneg_left hl
        · simp only [lt_iff, left_coe_zero, lt_iff_toRat, toRat_zero] at hneg
          norm_cast; simp only [Left.neg_pos_iff]; exact hneg
        · simp only [Rat.cast_neg, neg_le_neg_iff, hy.right]
      apply le_trans _ h₀
      norm_cast; simp only [divWithPrec]
      split_ifs with h
      · exfalso; grind only [haszero_iff_not_zerofree]
      · let l := (quotientEndpoints I J).min' (quotient_endpoints_nonempty I J)
        have h₁ : l ≤ I.right.toRat / J.right.toRat := by
          simp only [l]; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]
        apply le_trans _ h₁
        simp only [l]; exact Rat.toRat_toDyadic_le

    · have h₀ : (I.right.toRat : ℝ) / J.left.toRat ≤ ↑I.right.toRat / y := by
        rw [← (neg_neg J.left.toRat), ← (neg_neg y), Rat.cast_neg]
        rw [← (neg_neg I.right.toRat), Rat.cast_neg, neg_div_neg_eq, neg_div_neg_eq]
        apply div_le_div_of_nonneg_left
        · simp only [Rat.cast_neg, Left.nonneg_neg_iff, hr]
        · grind only [Left.neg_pos_iff, neg_of_mem_neg]
        · simp only [Rat.cast_neg, neg_le_neg_iff, hy.left]
      apply le_trans _ h₀
      norm_cast; simp only [divWithPrec]
      split_ifs with h
      · exfalso; grind only [haszero_iff_not_zerofree]
      · let l := (quotientEndpoints I J).min' (quotient_endpoints_nonempty I J)
        have h₁ : l ≤ I.right.toRat / J.left.toRat := by
          simp only [l]; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        apply le_trans _ h₁
        simp only [l]; exact Rat.toRat_toDyadic_le

lemma left_div_le_div_right' (hneg : J < 0) (y : ℝ) (hy : y ∈ J):
  ↑I.left.toRat / y ≤ ↑(divWithPrec prec I J).right.toRat := by
    rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
    · have h₀ : I.left.toRat / y ≤ (I.left.toRat : ℝ) / J.left.toRat := by
        rw [← (neg_neg J.left.toRat), Rat.cast_neg, div_neg, ← (neg_neg y), div_neg, neg_le_neg_iff]
        apply div_le_div_of_nonneg_left hl
        · grind only [Left.neg_pos_iff, neg_of_mem_neg]
        · simp only [Rat.cast_neg, neg_le_neg_iff, hy.left]
      apply le_trans h₀
      norm_cast; simp only [divWithPrec]
      split_ifs with h
      · exfalso; grind only [haszero_iff_not_zerofree]
      · let r := (quotientEndpoints I J).max' (quotient_endpoints_nonempty I J)
        have h₁ : I.left.toRat / J.left.toRat ≤ r := by
          simp only [r]; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
        apply le_trans h₁
        simp only [r]; exact (le_of_lt Rat.lt_toRat_toDyadic_add)
    · have h₀ : I.left.toRat / y ≤ (I.left.toRat : ℝ) / J.right.toRat := by
        rw [← (neg_neg J.right.toRat), Rat.cast_neg, ← (neg_neg y)]
        rw [← (neg_neg I.left.toRat), Rat.cast_neg, neg_div_neg_eq, neg_div_neg_eq]
        apply div_le_div_of_nonneg_left
        · simp only [Rat.cast_neg, Left.nonneg_neg_iff, hr]
        · simp only [lt_iff, left_coe_zero, lt_iff_toRat, toRat_zero] at hneg
          norm_cast; simp only [Left.neg_pos_iff]; exact hneg
        · simp only [Rat.cast_neg, neg_le_neg_iff, hy.right]
      apply le_trans h₀
      norm_cast; simp only [divWithPrec]
      split_ifs with h
      · exfalso; grind only [haszero_iff_not_zerofree]
      · let r := (quotientEndpoints I J).max' (quotient_endpoints_nonempty I J)
        have h₁ : I.left.toRat / J.right.toRat ≤ r := by
          simp only [r]; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        apply le_trans h₁
        simp only [r]; exact (le_of_lt Rat.lt_toRat_toDyadic_add)

lemma neg_div_bounds {x y : ℝ} (hx : x ∈ I)(h₀ : y < 0) :
  I.right.toRat / y ≤ x / y ∧ x / y ≤ I.left.toRat / y :=
      ⟨div_le_div_of_nonpos_of_le (le_of_lt h₀) hx.right, div_le_div_of_nonpos_of_le (le_of_lt h₀) hx.left⟩

lemma pos_div_bounds {x y : ℝ} (hx : x ∈ I)(h₀ : 0 < y) :
  I.left.toRat / y ≤ x / y ∧ x / y ≤ I.right.toRat / y :=
      ⟨div_le_div_of_nonneg_right hx.left (le_of_lt h₀), div_le_div_of_nonneg_right hx.right (le_of_lt h₀)⟩

#check div_le_div_of_nonneg_left
#check div_le_div_of_nonneg_right

lemma nonpos_div_bounds {x y : ℝ} (hy : y ∈ J) (h₀ : x ≤ 0) :
  x / J.left.toRat ≤ x / y ∧ x / y ≤ x / J.right.toRat := by
  rename_i hJ
  rcases ((zerofree_iff J).mp hJ) with hneg | hpos
  · have hy' : y < 0 := neg_of_mem_neg J hneg y hy
    have : (J.right.toRat : ℝ)  < 0 := neg_of_mem_neg J hneg J.right.toRat J.right_mem
    rw [← neg_div_neg_eq, ← neg_div_neg_eq x y, ← neg_div_neg_eq x (J.right.toRat)]
    constructor
    · apply div_le_div_of_nonneg_left (by grind only) (by grind only)
      simp only [neg_le_neg_iff, hy.left]
    · apply div_le_div_of_nonneg_left (by grind only) _
      · simp only [neg_le_neg_iff, hy.right]
      · grind only
  · have hy' : 0 < y := (pos_of_mem_pos J hpos y hy)
    have : 0 < (J.left.toRat : ℝ) := (pos_of_mem_pos J hpos J.left.toRat J.left_mem)
    rw [← neg_neg x, neg_div, neg_div y (-x), neg_div _ (-x)]
    constructor
    · rw [neg_le_neg_iff]
      apply div_le_div_of_nonneg_left (by grind only)
      · grind only
      · simp only [hy.left]
    · rw [neg_le_neg_iff]
      apply div_le_div_of_nonneg_left (by grind only) (by grind only) hy.right

lemma nonneg_div_bounds {x y : ℝ} (hy : y ∈ J) (h₀ : 0 ≤ x) :
  x / J.right.toRat ≤ x / y ∧ x / y ≤ x / J.left.toRat := by
  rename_i hJ
  rcases ((zerofree_iff J).mp hJ) with hneg | hpos
  · have hy' : y < 0 := neg_of_mem_neg J hneg y hy
    have : (J.right.toRat : ℝ)  < 0 := neg_of_mem_neg J hneg J.right.toRat J.right_mem
    rw [← neg_neg (J.left.toRat : ℝ), div_neg, ← neg_neg y, div_neg, ← neg_neg (J.right.toRat : ℝ), div_neg]
    constructor
    · rw [neg_le_neg_iff]
      apply div_le_div_of_nonneg_left h₀ (by grind only)
      simp only [neg_le_neg_iff, hy.right]
    · rw [neg_le_neg_iff]
      apply div_le_div_of_nonneg_left h₀ (by grind only)
      simp only [neg_le_neg_iff, hy.left]
  · have hy' : 0 < y := (pos_of_mem_pos J hpos y hy)
    have : 0 < (J.left.toRat : ℝ) := (pos_of_mem_pos J hpos _ J.left_mem)
    constructor
    · exact div_le_div_of_nonneg_left h₀ hy' hy.right
    · exact div_le_div_of_nonneg_left h₀ this hy.left


theorem div_sound : ∀ x ∈ I, ∀ y ∈ J, x / y ∈ divWithPrec prec I J := by
  intro x hx y hy; rename_i hJ
  rcases ((zerofree_iff J).mp hJ) with hneg | hpos
  -- J is negative
  · have h₀ : y < 0 := neg_of_mem_neg J hneg y hy
    have h₁ := neg_div_bounds I hx h₀
    constructor
    · apply le_trans (div_left_le_right_div' I J prec hneg y hy) h₁.left
    · apply le_trans h₁.right (left_div_le_div_right' I J prec hneg y hy)
  -- J is positive
  · have h₀ : 0 < y := (pos_of_mem_pos J hpos y hy)
    have h₁ := pos_div_bounds I hx h₀
    constructor
    · exact le_trans (div_left_le_left_div' I J prec hpos y hy) h₁.left
    · exact le_trans h₁.right (right_div_le_div_right' I J prec hpos y hy)

lemma quotientEndpoints_bounds_mono_left (hI : I ⊆ A) :
  ∀ y ∈ quotientEndpoints I J, (quotientEndpoints A J).min' (quotient_endpoints_nonempty A J) ≤ y ∧ y ≤ (quotientEndpoints A J).max' (quotient_endpoints_nonempty A J) := by
    intro y hy; rename_i hJ
    simp only [quotientEndpoints, mem_insert, mem_singleton] at hy
    rcases ((zerofree_iff J).mp hJ) with hneg | hpos
    · have hl : (J.left.toRat : ℝ) < 0 := (neg_of_mem_neg J hneg J.left.toRat J.left_mem)
      have hr : (J.right.toRat : ℝ) < 0 := (neg_of_mem_neg J hneg J.right.toRat J.right_mem)

      rcases hy with rfl | rfl | rfl | rfl
      · have : A.right.toRat / J.left.toRat ≤ I.left.toRat / J.left.toRat ∧
          I.left.toRat / J.left.toRat ≤ A.left.toRat / J.left.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (neg_div_bounds A _ hl)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.left_mem
        constructor
        · apply le_trans _ this.left
          simp only [min'_le, quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right
          simp only [le_max', quotientEndpoints, mem_insert, mem_singleton, true_or]

      · have : A.right.toRat / J.right.toRat ≤ I.left.toRat / J.right.toRat ∧
          I.left.toRat / J.right.toRat ≤ A.left.toRat / J.right.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (neg_div_bounds A _ hr)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.left_mem
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]

      · have : A.right.toRat / J.left.toRat ≤ I.right.toRat / J.left.toRat ∧
          I.right.toRat / J.left.toRat ≤ A.left.toRat / J.left.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (neg_div_bounds A _ hl)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.right_mem
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]

      · have : A.right.toRat / J.right.toRat ≤ I.right.toRat / J.right.toRat ∧
          I.right.toRat / J.right.toRat ≤ A.left.toRat / J.right.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (neg_div_bounds A _ hr)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.right_mem
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]

    · have hl : 0 < (J.left.toRat : ℝ) := (pos_of_mem_pos J hpos J.left.toRat J.left_mem)
      have hr : 0 < (J.right.toRat : ℝ) := (pos_of_mem_pos J hpos J.right.toRat J.right_mem)

      rcases hy with rfl | rfl | rfl | rfl
      · have : A.left.toRat / J.left.toRat ≤ I.left.toRat / J.left.toRat ∧
          I.left.toRat / J.left.toRat ≤ A.right.toRat / J.left.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (pos_div_bounds A _ hl)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.left_mem
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]

      · have : A.left.toRat / J.right.toRat ≤ I.left.toRat / J.right.toRat ∧
          I.left.toRat / J.right.toRat ≤ A.right.toRat / J.right.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (pos_div_bounds A _ hr)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.left_mem
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]

      · have : A.left.toRat / J.left.toRat ≤ I.right.toRat / J.left.toRat ∧
          I.right.toRat / J.left.toRat ≤ A.right.toRat / J.left.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (pos_div_bounds A _ hl)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.right_mem
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]

      · have : A.left.toRat / J.right.toRat ≤ I.right.toRat / J.right.toRat ∧
          I.right.toRat / J.right.toRat ≤ A.right.toRat / J.right.toRat := by
          simp only [← Rat.cast_le (K := ℝ), Rat.cast_div]
          apply (pos_div_bounds A _ hr)
          exact Set.mem_of_subset_of_mem ((subset_iff I A).mp hI) I.right_mem
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]

lemma num_div_isotonic (hI : I ⊆ A) : (divWithPrec prec I J) ⊆ (divWithPrec prec A J) := by
  simp only [subset_iff_endpts, divWithPrec]
  rcases haszero_or_zerofree J with hJ | hJ
  · exfalso; grind only [haszero_iff_not_zerofree]
  · rw [zerofree_iff_not_haszero] at hJ
    simp only [hJ, ↓reduceIte]
    constructor
    · apply Rat.toDyadic_mono
      apply le_min'; intro y hy
      exact (quotientEndpoints_bounds_mono_left _ _ hI _ hy).left
    · apply add_le_add' _ (by rfl)
      apply Rat.toDyadic_mono
      apply max'_le; intro y hy
      exact (quotientEndpoints_bounds_mono_left _ _ hI _ hy).right

lemma quotientEndpoints_bounds_mono_right (hJ : J ⊆ B) :
  ∀ y ∈ quotientEndpoints I J, (quotientEndpoints I B).min' (quotient_endpoints_nonempty I B) ≤ y ∧ y ≤ (quotientEndpoints I B).max' (quotient_endpoints_nonempty I B) := by
    intro y hy; rename_i hJ' hB'
    simp only [quotientEndpoints, mem_insert, mem_singleton] at hy
    have h₀ := Set.mem_of_subset_of_mem ((subset_iff J B).mp hJ) J.left_mem
    have h₁ := Set.mem_of_subset_of_mem ((subset_iff J B).mp hJ) J.right_mem
    rcases hy with rfl | rfl | rfl | rfl
    -- I.left / J.left
    · rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
      · have := (nonneg_div_bounds B h₀ hl); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
      · have := (nonpos_div_bounds B h₀ hr); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
    -- I.left / J.right
    · rcases le_total 0 (I.left.toRat : ℝ) with hl | hr
      · have := (nonneg_div_bounds B h₁ hl); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
      · have := (nonpos_div_bounds B h₁ hr); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
    -- I.right / J.left
    · rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
      · have := (nonneg_div_bounds B h₀ hl); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
      · have := (nonpos_div_bounds B h₀ hr); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]
    -- I.right / J.right
    · rcases le_total 0 (I.right.toRat : ℝ) with hl | hr
      · have := (nonneg_div_bounds B h₁ hl); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
      · have := (nonpos_div_bounds B h₁ hr); norm_cast at this
        constructor
        · apply le_trans _ this.left; apply min'_le
          simp only [quotientEndpoints, mem_insert, mem_singleton, true_or, or_true]
        · apply le_trans this.right; apply le_max'
          simp only [quotientEndpoints, mem_insert, mem_singleton, or_true]

lemma denom_div_isotonic (hJ : J ⊆ B) : (divWithPrec prec I J) ⊆ (divWithPrec prec I B) := by
  simp only [subset_iff_endpts, divWithPrec]
  rcases haszero_or_zerofree J with hJ' | hJ'
  · exfalso; grind only [haszero_iff_not_zerofree]
  · have hB' : B.ZeroFree := by grind only
    rw [zerofree_iff_not_haszero] at hJ' hB'
    simp only [hJ', hB', ↓reduceIte]
    constructor
    · apply Rat.toDyadic_mono
      apply le_min'; intro y hy
      exact (quotientEndpoints_bounds_mono_right I J hJ y hy).left
    · apply add_le_add' _ (by rfl)
      apply Rat.toDyadic_mono
      apply max'_le; intro y hy
      exact (quotientEndpoints_bounds_mono_right I J hJ y hy).right

theorem div_isotonic (hI : I ⊆ A) (hJ : J ⊆ B) :
  (divWithPrec prec I J) ⊆ (divWithPrec prec A B) := by
  apply DyadicInterval.subset_trans
  · apply num_div_isotonic I J prec hI
  · apply denom_div_isotonic A J prec hJ

end Division

open DyadicInterval
def A : DyadicInterval := ⟨(4 : ℚ).toDyadic 1, (5 : ℚ).toDyadic 1, by rfl⟩
def B : DyadicInterval := ⟨(1 : ℚ).toDyadic 1, (1 : ℚ).toDyadic 1, by rfl⟩
#check neg_neg (2 : ℝ)
#eval! A
#eval! B
#eval! divWithPrec 4 A B
