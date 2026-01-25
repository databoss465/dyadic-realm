import Mathlib
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false

/-!
# Polynomial Bounds over Dyadic Intervals
This file defines polynomials with rational coefficients represented as fixed-length vectors,
and provides functions to evaluate these polynomials over dyadic intervals with guaranteed soundness.

## Main Definitions
- `RatPol n` : Type alias for `Vector ℚ n`, representing polynomials of degree ≤ n-1.
- `toPoly` : Converts a `RatPol n` to a `Polynomial ℚ`.
- `toRealPoly` : Converts a `RatPol n` to a `Polynomial ℝ`.
- `deriv` : Computes the derivative of a `RatPol n`.

- `evalWithPrec` : Evaluates a `RatPol n` at a rational point, returning a `DyadicInterval` at specified precision.
- `intervalEvalWithPrec` : Evaluates a `RatPol n` over a `DyadicInterval`; precision is specified for handling the conversion of rationals to dyadic intervals.

## Main Theorems
- `eval_sound` : Ensures that the evaluation of `toRealPoly` at a rational point lies within the computed dyadic interval.
- `interval_eval_sound` : Ensures that the evaluation of `toRealPoly` over a dyadic interval lies within the computed dyadic interval.
-/

abbrev RatPol (n : ℕ) := Vector ℚ n -- degree ≤ n-1

namespace RatPol
open DyadicInterval Dyadic Vector Polynomial

/-- Convert a rational polynomial represented as a vector to a `Polynomial ℚ`. -/
noncomputable def toPoly {n : ℕ} (p : RatPol n) : Polynomial ℚ := Polynomial.ofFn n p.get

/-- Convert a rational polynomial represented as a vector to a `Polynomial ℝ`. -/
noncomputable def toRealPoly {n : ℕ} (p : RatPol n) : Polynomial ℝ := (toPoly p).map (algebraMap ℚ ℝ)

/-- The polynomial of degree 0 is the zero polynomial -/
lemma to_poly_trivial (p : RatPol 0) : (toPoly p) = 0 := by
  simp only [toPoly]; apply Polynomial.ext
  grind only [Polynomial.coeff_zero, Polynomial.ofFn_coeff_eq_zero_of_ge]

lemma to_real_poly_trivial (p : RatPol 0) : (toRealPoly p) = 0 := by
  simp only [toRealPoly]
  rw [Polynomial.map_eq_zero_iff]
  · exact to_poly_trivial p
  · exact Rat.cast_injective

/-- Coefficient extraction for `toPoly` -/
lemma to_poly_coeff {n : ℕ} (p : RatPol n) (k : ℕ) :
  (toPoly p).coeff k = if h : k < n then (p.get ⟨k,h⟩) else 0 := by
  unfold toPoly
  split_ifs with h
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ h]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by grind only)]

/-- Coefficient extraction for `toRealPoly` -/
lemma to_real_poly_coeff {n : ℕ} (p : RatPol n) (k : ℕ) :
  (toRealPoly p).coeff k =
    if h : k < n then ↑(p.get ⟨k,h⟩) else 0 := by
    unfold toRealPoly
    simp only [Polynomial.coeff_map, to_poly_coeff]
    simp only [eq_ratCast]
    split_ifs with h
    · norm_cast
    · norm_cast

/-- Find the first non-zero coefficient of the rational polynomial (excluding constant term) -/
def firstNonzeroCoeff {n : ℕ} (p : RatPol n) := p.tail.toList.find? (fun x ↦ x ≠ 0)

/-- Find the index of the first non-zero coefficient of the rational polynomial (excluding constant term)
This returns the index in tail, so for actual index, use `firstNonzeroIdx + 1`
-/
def firstNonzeroIdx {n : ℕ} (p : RatPol n) := p.tail.toList.findIdx? (fun x ↦ x ≠ 0)

/-- The index of the first non-zero coefficient is less than the degree -/
lemma firstNonzeroIdx_lt {m : ℕ} {k : ℕ} (p : RatPol (m +1)) : firstNonzeroIdx p = some k → k < m := by
  intro hk; unfold firstNonzeroIdx at hk
  rw [List.findIdx?_eq_some_iff_getElem] at hk
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
    getElem_extract, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Decidable.not_not, length_toList] at hk
  grind only

/-- If the count of non-zero coefficients in the tail is one, then there exists a non-zero coefficient (excluding constant term) -/
theorem countP_eq_one_exists_firstNonzero
  {m : ℕ} (p : RatPol (m+1)) (heq : p.tail.countP (fun x ↦ decide (x ≠ 0)) = 1):
  ∃ a k, firstNonzeroCoeff p = some a ∧ firstNonzeroIdx p = some k := by
  have h :  0 < p.tail.toList.countP (fun x ↦ decide (x ≠ 0)) := by grind only [Vector.countP_toList]
  have h := List.countP_pos_iff.mp h
  have ha_some : (firstNonzeroCoeff p).isSome := by
    unfold firstNonzeroCoeff
    rw [List.find?_isSome]
    rcases h with ⟨a, hmem, hp⟩; use a
  have hk_some : (firstNonzeroIdx p).isSome := by
    unfold firstNonzeroIdx
    rw [List.findIdx?_isSome, List.any_eq_true]
    rcases h with ⟨a, hmem, hp⟩; use a
  rcases Option.isSome_iff_exists.mp ha_some with ⟨a, ha⟩
  rcases Option.isSome_iff_exists.mp hk_some with ⟨k, hk⟩
  use a, k

/-- If the count of non-zero coefficients in the tail is one, then the coefficient at `firstNonzeroIdx` is `firstNonzeroCoeff` -/
lemma countP_eq_one_tail_get_nonzero
  {m : ℕ} {a : ℚ} {k : ℕ} {i' : Fin m}(p : RatPol (m+1)) (hcoeff : firstNonzeroCoeff p = some a)
  (hidx : firstNonzeroIdx p = some k) (heq : p.tail.countP (fun x ↦ decide (x ≠ 0)) = 1) (hk : i'.val = k):
  p.tail.get i' = a := by
  let ⟨i, hi⟩ := i'
  simp only at hk
  simp only [hk]
  unfold firstNonzeroCoeff at hcoeff
  obtain ⟨h₁, k', hk₁, hk₂, hk₃⟩ := (List.find?_eq_some_iff_getElem).mp hcoeff
  unfold firstNonzeroIdx at hidx
  obtain ⟨h₂, hk₄, hk₅⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx

  simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h₁
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast, getElem_extract,
    _root_.add_comm] at hk₂
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast, getElem_extract,
    ne_eq, decide_not, Bool.not_not, decide_eq_true_eq] at hk₃
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast, getElem_extract,
    ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hk₄
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast, getElem_extract,
    ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Decidable.not_not] at hk₅
  simp only [Vector.get_tail, Fin.succ_mk]
  simp only [get_eq_getElem, ← hk₂]
  have : k' = k := by
    apply le_antisymm
    · by_contra hk'
      have : p[1 + k] = 0 := hk₃ k (not_le.mp hk')
      grind only
    · by_contra hk'
      have : p[1 + k'] = 0 := hk₅ k' (not_le.mp hk')
      grind only
  simp only [this]

/-- If the count of non-zero coefficients in the tail is one, then the coefficient at indices not equal to `firstNonzeroIdx` is zero -/
lemma countP_eq_one_tail_get_zero
  {m : ℕ} {a : ℚ} {k : ℕ} {i' : Fin m}(p : RatPol (m+1)) (hcoeff : firstNonzeroCoeff p = some a)
  (hidx : firstNonzeroIdx p = some k) (heq : p.tail.countP (fun x ↦ decide (x ≠ 0)) = 1) (hk : i'.val ≠ k):
  p.tail.get i' = 0 := by
  let ⟨i, hi⟩ := i'; by_contra hi'
  have hi : i < (tail p).toList.length := by simp only [Nat.add_one_sub_one, length_toList, hi]
  simp only at hk
  unfold firstNonzeroIdx at hidx
  obtain ⟨hk₁, hk₂, hk₃⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
  -- simp only [Nat.add_one_sub_one, tail_eq_cast_extract, length_toList] at hk₁
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
    getElem_extract, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at hk₂
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
    getElem_extract, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Decidable.not_not] at hk₃
  rw [← Vector.countP_toList] at heq
  simp only [Vector.get_tail, Fin.succ_mk] at hi'
  simp only [Vector.get_eq_getElem] at hi'
  have hk : k < i := by
    rcases lt_or_lt_iff_ne.mpr hk with hl | hr
    · grind only
    · exact hr

  let l := (tail p).toList
  have h_left : 1 ≤ List.countP (fun x ↦ decide (x ≠ 0)) (l.take (k + 1)) := by
    rw [List.one_le_countP_iff]; use l[k]
    constructor
    · simp only [l]
      rw [List.mem_take_iff_getElem]; use k
      simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
        getElem_extract, length_toList, lt_inf_iff, lt_add_iff_pos_right, zero_lt_one, true_and,
        exists_prop, and_true]
      grind only
    · simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
      getElem_extract, ne_eq, hk₂, not_false_eq_true, decide_true, l]

  have h_right : 1 ≤ List.countP (fun x ↦ decide (x ≠ 0)) (l.drop (k + 1)) := by
    rw [List.one_le_countP_iff]; use l[i]
    constructor
    · rw [List.mem_drop_iff_getElem ]; use i - (k + 1)
      grind only

    · simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
      getElem_extract, _root_.add_comm, ne_eq, hi', not_false_eq_true, decide_true, l]

  have h₂ : 2 ≤ List.countP (fun x ↦ decide (x ≠ 0)) l := by
    nth_rw 1 [← List.take_append_drop (k + 1) l]
    rw [List.countP_append]
    grind only
  grind only

/-- If the count of non-zero coefficients in the tail is one, then every coefficient except at `firstNonzeroIdx` is zero, and at `firstNonzeroIdx` is `firstNonzeroCoeff` -/
theorem countP_eq_one_tail_get
  {m : ℕ} {a : ℚ} {k : ℕ} (p : RatPol (m+1)) (hcoeff : firstNonzeroCoeff p = some a)
  (hidx : firstNonzeroIdx p = some k) (heq : p.tail.countP (fun x ↦ decide (x ≠ 0)) = 1) :
  ∀ i : Fin m, p.tail.get i = if (i.val = k) then a else 0 := by
  grind only [countP_eq_one_tail_get_nonzero, countP_eq_one_tail_get_zero]

/-- If the count of non-zero coefficients in the tail is one, then `toPoly` is of the form $C + a x^{k+1}$ -/
theorem countP_eq_one_to_poly
  {m : ℕ} {a : ℚ} {k : ℕ} (p : RatPol (m+1)) (hcoeff : firstNonzeroCoeff p = some a)
  (hidx   : firstNonzeroIdx p = some k) (heq : p.tail.countP (fun x ↦ decide (x ≠ 0)) = 1) :
  toPoly p = Polynomial.C p.head + Polynomial.monomial (k + 1) a := by
  apply Polynomial.ext; intro n
  simp only [coeff_add, coeff_C, coeff_monomial]
  split_ifs with h₁ h₂ h₂
  · exfalso; grind only
  · simp only [h₁, _root_.add_zero, toPoly]
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by grind only)]; rfl

  · simp only [_root_.zero_add, ← h₂, toPoly]
    have hk : k < m := firstNonzeroIdx_lt p hidx
    have h := countP_eq_one_tail_get p hcoeff hidx heq ⟨k, hk⟩
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.succ_lt_succ hk)]
    simp only [Vector.get_tail, Fin.succ_mk, ↓reduceIte] at h
    grind only

  · simp only [_root_.zero_add]
    by_cases hnm : n < m + 1
    · rw [toPoly, Polynomial.ofFn_coeff_eq_val_of_lt _ hnm]
      cases n with
      | zero => grind only
      | succ j =>
        simp only [add_lt_add_iff_right] at hnm
        simp only [Nat.add_right_cancel_iff] at h₂
        have h := countP_eq_one_tail_get p hcoeff hidx heq ⟨j, hnm⟩
        simp only [Vector.get_tail, Fin.succ_mk] at h
        grind only

    · grind only [toPoly, Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- If the count of non-zero coefficients in the tail is one, then `toRealPoly` is of the form $C + a x^{k+1}$ -/
theorem countP_eq_one_to_real_poly
  {m : ℕ} {a : ℚ} {k : ℕ} (p : RatPol (m+1)) (hcoeff : firstNonzeroCoeff p = some a)
  (hidx   : firstNonzeroIdx p = some k) (heq : p.tail.countP (fun x ↦ decide (x ≠ 0)) = 1) :
  toRealPoly p = Polynomial.C (p.head : ℝ) + Polynomial.monomial (k + 1) (a : ℝ) := by
  apply Polynomial.ext; intro n
  unfold toRealPoly
  rw [countP_eq_one_to_poly p hcoeff hidx heq]
  simp only [coeff_map, coeff_add, coeff_C, coeff_monomial]
  split_ifs
  · simp only [eq_ratCast, Rat.cast_add]
  · simp only [_root_.add_zero, eq_ratCast]
  · simp only [_root_.zero_add, eq_ratCast]
  · simp only [_root_.add_zero, eq_ratCast, Rat.cast_zero]

/-- Derivative of rational polynomial represented as vector -/
def deriv {n : ℕ} (p : RatPol n) := p.tail.mapIdx (fun i c => c * ((i : ℚ) + 1))

/-- Correctness of derivative definition w.r.t. `toPoly` -/
theorem deriv_eq_poly_deriv {n : ℕ} (p : RatPol n) : toPoly (deriv p) = (toPoly p).derivative := by
  apply Polynomial.ext; intro k
  simp only [Polynomial.coeff_derivative, toPoly]
  by_cases h : k < n - 1
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ h]
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by grind only)]
    simp only [deriv, Vector.get, tail_eq_cast_extract, toArray_mapIdx, toArray_cast, toArray_extract, Fin.cast_mk, Array.getElem_mapIdx, Array.getElem_extract, getElem_toArray, mul_eq_mul_right_iff]
    left; grind only
  · rw [not_lt] at h
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ h]
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by grind only)]
    simp only [MulZeroClass.zero_mul]

/-- Correctness of derivative definition w.r.t. `toRealPoly` -/
theorem deriv_eq_real_poly_deriv {n : ℕ} (p : RatPol n) :
  toRealPoly (deriv p) = (toRealPoly p).derivative := by
  simp only [toRealPoly, Polynomial.derivative_map, deriv_eq_poly_deriv]

/-- Mean Value Theorem for rational polynomials represented as vectors -/
theorem mvt_real_poly {n : ℕ} (p : RatPol n) (I : DyadicInterval) (x : ℝ) (hx : x ∈ I) :
  ∃ ξ ∈ I, (toRealPoly p).eval x = (toRealPoly (deriv p)).eval ξ * (x - ↑I.midpoint.toRat) +
    (toRealPoly p).eval ↑I.midpoint.toRat := by
    by_cases hm : x = ↑I.midpoint.toRat
    · use ↑I.midpoint.toRat, I.midpoint_mem
      simp only [hm, sub_self, MulZeroClass.mul_zero, _root_.zero_add]

    · rw [← ne_eq, ← lt_or_lt_iff_ne] at hm
      rcases hm with hm | hm
      · have hfc : ContinuousOn (toRealPoly p).eval (Set.Icc x I.midpoint.toRat) := by
          apply Polynomial.continuousOn
        have hfd : DifferentiableOn ℝ (toRealPoly p).eval (Set.Ioo x I.midpoint.toRat) := by
          apply Polynomial.differentiableOn
        obtain ⟨ξ, hξ, h⟩ := exists_deriv_eq_slope (toRealPoly p).eval hm hfc hfd
        use ξ; simp only [Polynomial.deriv, ← deriv_eq_real_poly_deriv] at h
        constructor
        · rw [mem_iff_le_endpts] at *
          rw [Set.mem_Ioo] at hξ
          constructor
          · grind only
          · apply le_trans hξ.right.le; norm_cast
            exact toRat_le_toRat_iff.mpr I.midpoint_le_right
        · grind only

      · have hfc : ContinuousOn (toRealPoly p).eval (Set.Icc I.midpoint.toRat x) := by
          apply Polynomial.continuousOn
        have hfd : DifferentiableOn ℝ (toRealPoly p).eval (Set.Ioo I.midpoint.toRat x) := by
          apply Polynomial.differentiableOn
        obtain ⟨ξ, hξ, h⟩ := exists_deriv_eq_slope (toRealPoly p).eval hm hfc hfd
        simp only [Polynomial.deriv, ← deriv_eq_real_poly_deriv] at h
        use ξ; constructor
        · rw [mem_iff_le_endpts] at *
          rw [Set.mem_Ioo] at hξ
          constructor
          · apply le_trans _ hξ.left.le; norm_cast
            exact toRat_le_toRat_iff.mpr I.left_le_midpoint
          · grind only
        · grind only


-- Horner's method => This will actually be used in computation
-- But still consider not using foldr, and using direct evaluation
/-- Evaluate rational polynomial at a rational point, as a `DyadicInterval` with endpoints at a given precision -/
def evalWithPrec {n : ℕ} (prec : ℤ) (p : RatPol n) (x : ℚ) : DyadicInterval :=
  -- let px := p.foldr (fun coeff acc ↦ coeff + x * acc) 0
  let px := ∑ i : Fin n, (p.get i) * x ^ (i : ℕ)
  ofRatWithPrec prec px

/-- Evaluation of `toRealPoly` at rational point matches direct evaluation -/
theorem eval_to_real_poly {n : ℕ} (prec : ℤ) (p : RatPol n) (x : ℚ):
  (toRealPoly p).eval ↑x = ∑ i : Fin n, (p.get i) * x ^ (i : ℕ) := by
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]
  simp only [Finset.sum_fin_eq_sum_range]
  simp only [eval_eq_sum, Polynomial.sum.eq_1]
  have hcoeff : ∀ k, (toRealPoly p).coeff k * (x:ℝ)^k = if h : k < n then
    ↑(p.get ⟨k,h⟩) * (x:ℝ)^k else 0 := by grind only [to_real_poly_coeff]
  simp only [hcoeff]
  rw [Finset.sum_subset]
  · rw [Finset.subset_range]
    intro k hk
    rw [Polynomial.mem_support_iff] at hk
    by_contra hkn
    grind only [to_real_poly_coeff]
  · intro k hk hk'
    rw [Finset.mem_range] at hk
    simp only [mem_support_iff, ne_eq, Decidable.not_not, to_real_poly_coeff] at hk'
    grind only

/-- Soundness of polynomial evaluation over rationals -/
theorem eval_sound {n : ℕ} (prec : ℤ) (p : RatPol n) (x : ℚ) :
  (toRealPoly p).eval ↑x ∈ evalWithPrec prec p x := by
  unfold evalWithPrec
  rw [eval_to_real_poly prec]
  apply rat_mem_of_rat

-- def eval' {n : ℕ} (p : RatPol n) (z : ℝ) : ℝ := p.foldr (fun coeff acc ↦ ↑coeff + z * acc) 0
-- theorem eval_eq_poly_eval {n : ℕ} (p : RatPol n) (z : ℝ) : eval' p z = (toPoly p).aeval z := by sorry

/-- If the polynomial is constant, then `toPoly` is the constant term -/
theorem const_to_poly {m : ℕ} (p : RatPol (m +1)) (hp : p.tail.countP (· ≠ 0) = 0) :
  toPoly p = Polynomial.C p.head := by
  apply Polynomial.ext; intro k
  simp only [toPoly]
  cases k with
  | zero =>
    rw [Polynomial.coeff_C_zero, Polynomial.ofFn_coeff_eq_val_of_lt _ (by linarith)]; rfl

  | succ j =>
    rw [Polynomial.coeff_C_succ]
    simp only [Nat.add_one_sub_one, ne_eq, decide_not, ← countP_toList,
      List.countP_eq_zero, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Decidable.not_not, mem_toList_iff, mem_iff_getElem] at hp
    by_cases h : j + 1 < m + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ h]; apply hp
      use j, (Nat.lt_of_succ_lt_succ h)
      simp only [tail, Nat.add_one_sub_one, getElem_cast, getElem_extract, Vector.get, Fin.cast_mk,
        getElem_toArray]
      grind only
    · grind only [Polynomial.ofFn_coeff_eq_zero_of_ge]

/-- If the polynomial is constant, then `toRealPoly` is the constant term -/
theorem const_to_real_poly {m : ℕ} (p : RatPol (m +1)) (hp : p.tail.countP (· ≠ 0) = 0) :
  toRealPoly p = Polynomial.C ↑p.head := by
  unfold toRealPoly
  rw [const_to_poly _ hp]
  simp only [map_C, eq_ratCast]

/-- Evaluate rational polynomial over a dyadic interval, producing a dyadic interval at given precision -/
def intervalEvalWithPrec {n : ℕ} (prec : ℤ) (p : RatPol n) (I : DyadicInterval) : DyadicInterval :=
  match n with
  | 0 => 0
  | m + 1 =>
    -- Count non-zero coefficients
    match p.tail.countP (· ≠ 0) with
    | 0 => ofRatWithPrec prec p.head -- Constant Polynomial
    | 1 => -- Constant + Monomial : c + a * I ^ (k+1)
      let a := firstNonzeroCoeff p
      let k := firstNonzeroIdx p
      match a, k with
      | some a, some k =>  ofRatWithPrec prec p.head + (ofRatWithPrec prec a) * I ^ (k + 1)
      | _, _ => 0 -- Unreachable
    | _ => --Centered form : p(m) + p'(I) * (I - c)
      (evalWithPrec prec p I.midpoint.toRat) + (intervalEvalWithPrec prec (deriv p) I) * (I - I.midpoint)
    -- p(m) + p'(I) * (I - c)

/-- Soundness of polynomial evaluation over dyadic intervals -/
theorem interval_eval_sound (prec : ℤ) {n : ℕ} (p : RatPol n) (I : DyadicInterval) :
  ∀ x ∈ I, (toRealPoly p).eval x ∈ intervalEvalWithPrec prec p I := by
  intro x hx
  unfold intervalEvalWithPrec
  match n with
  | 0 =>
    simp only [to_real_poly_trivial, Polynomial.eval_zero] at *
    rw [mem_iff_le_endpts]; norm_cast
  | m + 1 =>
    simp only
    split
    · rename_i hp
      rw [const_to_real_poly p hp]
      simp only [Polynomial.eval_C, rat_mem_of_rat]
    · split
      · rename_i _ h _ _ a k ha hk
        rw [countP_eq_one_to_real_poly p ha hk h]
        simp only [eval_add, eval_C, eval_monomial]
        apply add_sound
        · apply rat_mem_of_rat
        · apply mul_sound
          · apply rat_mem_of_rat
          · apply pow_sound I (k + 1) x hx
      · rename_i heq _ _ hf
        exfalso
        obtain ⟨a, k, ha, hk⟩ := countP_eq_one_exists_firstNonzero p heq
        exact hf a k ha hk
    · obtain ⟨c, hc, h⟩ := mvt_real_poly p I x hx
      rw [h, DyadicInterval.add_comm]
      apply add_sound
      · apply mul_sound
        · apply interval_eval_sound
          exact hc
        · apply sub_sound
          · exact hx
          · simp only [ofDyadic, mem_iff_le_endpts, le_refl, and_self]
      · apply eval_sound

theorem interval_eval_sound' (prec : ℤ) {n : ℕ} (p : RatPol n) (I : DyadicInterval) :
  (toRealPoly p).eval '' I.toSet ⊆ intervalEvalWithPrec prec p I := by
    intro x hx
    simp only [Set.mem_image] at hx
    obtain ⟨y, hy, hy'⟩ := hx
    rw [← hy']
    apply interval_eval_sound; exact hy



end RatPol
