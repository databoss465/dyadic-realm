import Mathlib
open Dyadic
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
section
open Finset

-- toRat_ofOdd_eq_mul_two_pow : toRat (.ofOdd n k hn) = n * 2 ^ (-k)
theorem shiftRight_toRat (a : Dyadic) (i : Int) :
  (a.shiftRight i).toRat = a.toRat * 2 ^ (-i) := by
    unfold Dyadic.shiftRight
    cases a
    · simp only [Dyadic.zero_eq, toRat_zero, zpow_neg, zero_mul]
    · rename_i n k hn
      simp only [toRat_ofOdd_eq_mul_two_pow]
      rw [neg_add, zpow_add₀ (by grind only)]
      ring

def half (a : Dyadic) : Dyadic := a.shiftRight 1

theorem toRat_half (a : Dyadic) : (half a).toRat = a.toRat/2 := by
  rw [half, shiftRight_toRat]; ring

@[simp, grind]
theorem add_le_add' {a b c d : Dyadic} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  simp only [le_iff_toRat, toRat_add] at *
  exact add_le_add h₁ h₂

@[simp, grind]
lemma neg_le_iff {a b : Dyadic} : -a ≤ b ↔ -b ≤ a := by
  simp only [le_iff_toRat, toRat_neg]
  exact neg_le

@[simp, grind]
lemma le_neg_iff {a b : Dyadic} : a ≤ -b ↔ b ≤ -a := by
  simp only [le_iff_toRat, toRat_neg]
  exact le_neg

@[simp, grind]
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

@[simp, grind]
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

lemma toRat_eq {a b : Dyadic} :  a = b ↔ a.toRat = b.toRat  := by
  constructor
  · intro h
    rw [le_antisymm_iff] at *
    simp only [← le_iff_toRat, h, and_true]
  · intro h
    rw [le_antisymm_iff] at *
    simp only [le_iff_toRat, h, and_true]

@[simp, grind]
lemma toRat_max {a b : Dyadic} : (max a b).toRat = max a.toRat b.toRat := by
  rcases le_total a b with ha | hb
  · rw [max_eq_right ha, max_eq_right]
    rw [← le_iff_toRat]; exact ha
  · rw [max_eq_left hb, max_eq_left]
    rw [← le_iff_toRat]; exact hb


@[simp, grind]
lemma toRat_min {a b : Dyadic} : (min a b).toRat = min a.toRat b.toRat := by
  rcases le_total a b with ha | hb
  · rw [min_eq_left ha, min_eq_left]
    rw [← le_iff_toRat]; exact ha
  · rw [min_eq_right hb, min_eq_right]
    rw [← le_iff_toRat]; exact hb

-- instance : AddCommGroup Dyadic :=
--   -- We tell Lean: "Dyadic is just a Group hidden inside Rat"
--   let h_inj : Function.Injective Dyadic.toRat := by
--     intro x y h
--     rw [toRat_eq] -- Your theorem that toRat is injective
--     exact h

--   Function.Injective.addCommGroup Dyadic.toRat h_inj
--     toRat_zero toRat_add toRat_neg (fun _ _ => rfl)

end
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

def formatDyadic (d : Dyadic) : String :=
  if (d.toRat).den == 1 then
    toString (d.toRat).num  -- Print "5" instead of "5/1"
  else
    s!"{(d.toRat).num}/{(d.toRat).den}"

-- 2. Define the Repr instance for the Interval
instance : Repr DyadicInterval where
  reprPrec I _ := s!"[{formatDyadic I.left}, {formatDyadic I.right}]"

@[simp, grind]
theorem eq_iff_left_right : I = J ↔ I.left = J.left ∧ I.right = J.right := by
  constructor
  · intro h; cases I; cases J
    simp only [mk.injEq] at *
    exact h
  · intro h; cases I; cases J
    simp only [mk.injEq] at *
    exact h

@[simp, grind] theorem isValid' : (I.left.toRat : ℝ) ≤ I.right.toRat := by simp only [Rat.cast_le, ← le_iff_toRat, I.isValid]

@[simp, grind] theorem isValid_toRat : I.left.toRat ≤ I.right.toRat := by simp only [← le_iff_toRat, I.isValid]

def ofDyadic : DyadicInterval := ⟨a, a, le_rfl⟩
instance : Coe Dyadic DyadicInterval := ⟨DyadicInterval.ofDyadic⟩

def ofRatWithPrec (prec : ℤ) (x : ℚ) : DyadicInterval :=
  let l := x.toDyadic prec
  let r := if l.toRat = x then l
    else l + Dyadic.ofIntWithPrec 1 prec
  have h : l ≤ r := by
    simp only [l, r]
    split_ifs with h
    · rfl
    · rw [le_iff_toRat]
      apply le_trans Rat.toRat_toDyadic_le
      exact (le_of_lt Rat.lt_toRat_toDyadic_add)
  ⟨l, r, h⟩

instance (n : Nat) : OfNat DyadicInterval n :=
  ⟨((n : Dyadic) : DyadicInterval)⟩

instance : NatCast DyadicInterval :=
  ⟨fun n => ((n : Dyadic) : DyadicInterval)⟩

instance : IntCast DyadicInterval :=
  ⟨fun z => ((z : Dyadic) : DyadicInterval)⟩

@[simp, grind] lemma left_coe_zero : (0 : DyadicInterval).left = 0 := by rfl

@[simp, grind] lemma right_coe_zero : (0 : DyadicInterval).right = 0 := by rfl

def toSet : Set ℝ := Set.Icc (I.left.toRat : ℝ) (I.right.toRat : ℝ)
instance : Coe DyadicInterval (Set ℝ) := ⟨toSet⟩

def Mem (x : ℝ) : Prop := x ∈ (I : Set ℝ)
instance : Membership ℝ DyadicInterval where mem := DyadicInterval.Mem

@[simp, grind]
theorem mem_iff_mem_Icc : ∀ x : ℝ, x ∈ I ↔ x ∈ Set.Icc (I.left.toRat : ℝ) (I.right.toRat : ℝ) := by
  intro x; rfl

@[simp, grind]
theorem mem_iff_le_endpts : ∀ x : ℝ, x ∈ I ↔ I.left.toRat ≤ x ∧ x ≤ I.right.toRat := by intro x; rfl

@[simp, grind] lemma left_mem : ↑I.left.toRat ∈ I := by
  simp only [mem_iff_le_endpts, le_refl, true_and, I.isValid']

@[simp, grind] lemma right_mem : ↑I.right.toRat ∈ I := by
  simp only [mem_iff_le_endpts, le_refl, and_true, I.isValid']

theorem rat_mem_of_rat (x: ℚ) (prec : ℤ) : (x : ℝ) ∈ ofRatWithPrec prec x := by
  simp only [mem_iff_le_endpts, ofRatWithPrec]
  norm_cast
  split_ifs with h
  · grind only [cases Or]
  · exact ⟨Rat.toRat_toDyadic_le, le_of_lt Rat.lt_toRat_toDyadic_add⟩

theorem nonempty : Nonempty (I : Set ℝ) := ⟨↑I.left.toRat, I.left_mem⟩

@[ext] theorem ext : (I : Set ℝ) = ↑J → I = J := by
  intro h
  simp only [toSet] at h
  rw [Set.Icc_eq_Icc_iff] at h
  · norm_cast at h
    simp only [← toRat_eq] at h
    rw [eq_iff_left_right]
    exact h
  · exact I.isValid'

def width : Dyadic := I.right - I.left

theorem width_nonneg : 0 ≤ I.width := by
  simp only [width, le_iff_toRat, toRat_sub, toRat_zero]; rw [sub_nonneg]
  exact I.isValid_toRat

def subset : Prop := J.left ≤ I.left ∧ I.right ≤ J.right
instance : HasSubset DyadicInterval := ⟨DyadicInterval.subset⟩
instance : HasSSubset DyadicInterval where SSubset I J := I ⊆ J ∧ I ≠ J

@[simp, grind] theorem subset_iff : I ⊆ J ↔ I.toSet ⊆ J.toSet := by
  simp only [toSet]
  rw [Set.Icc_subset_Icc_iff I.isValid']
  simp only [Rat.cast_le, ← le_iff_toRat]; rfl

@[simp, grind] theorem subset_iff_endpts : I ⊆ J ↔ J.left ≤ I.left ∧ I.right ≤ J.right := by rfl

@[simp, grind] theorem ssubset_iff : I ⊂ J ↔ I ⊆ J ∧ I ≠ J := by rfl

theorem subset_width : I ⊆ J → I.width ≤ J.width := by
  grind only [subset_iff_endpts, width, le_iff_toRat]

theorem subset_and_eq_width : I ⊆ J → I.width = J.width → I = J := by
  grind only [subset_iff_endpts, width, = Set.mem_Icc, eq_iff_left_right, isValid_toRat, isValid']

theorem ssubset_width : I ⊂ J → I.width < J.width := by
  intro h
  simp only [SSubset] at h
  rw [lt_iff_le_and_ne]
  constructor
  · exact subset_width I J h.left
  · by_contra h'
    grind only [subset_and_eq_width]

@[simp, grind] theorem subset_refl : I ⊆ I := by grind only [subset_iff, = Set.subset_def]
@[grind] theorem subset_trans : I ⊆ J → J ⊆ K → I ⊆ K := by grind only [subset_iff, = Set.subset_def]

def lt : Prop := I.right < J.left
instance : LT DyadicInterval := ⟨DyadicInterval.lt⟩

instance : Decidable (I < 0) :=
  if h : I.right < 0 then isTrue (by change I.right < 0; exact h)
  else isFalse (by change ¬I.right < 0; exact h)

instance : Decidable (0 < I) :=
  if h : 0 < I.left then isTrue (by change 0 < I.left; exact h)
  else isFalse (by change ¬0 < I.left; exact h)

class ZeroFree : Prop where p : (I < 0) ∨ (0 < I)
instance : Decidable (ZeroFree I) :=
  if h : (I < 0) ∨ (0 < I) then isTrue ⟨h⟩
  else isFalse (fun h_class => h h_class.p)

@[simp, grind] theorem zerofree_iff : ZeroFree I ↔ (I < 0 ∨ 0 < I) := by
  constructor
  · intro h; exact h.p
  · intro h; exact ⟨h⟩

class HasZero : Prop where p : I.left ≤ 0 ∧ 0 ≤ I.right
instance : Decidable (HasZero I) :=
  if h : I.left ≤ 0 ∧ 0 ≤ I.right then isTrue ⟨h⟩
  else isFalse (fun h_class => h h_class.p)

@[simp, grind] theorem haszero_iff : HasZero I ↔ I.left ≤ 0 ∧ 0 ≤ I.right := by
  constructor
  · intro h; exact h.p
  · intro h; exact ⟨h⟩

@[simp, grind] theorem haszero_iff_not_zerofree : HasZero I ↔ ¬ZeroFree I := by
  constructor
  · intro h
    rw [haszero_iff] at h
    rw [zerofree_iff, not_or]
    constructor
    · change ¬I.right < 0
      rw [not_lt]; exact h.right
    · change ¬0<I.left
      rw [not_lt]; exact h.left

  · intro h
    rw [zerofree_iff, not_or] at h
    rw [haszero_iff, ← not_lt, ← not_lt]
    constructor
    · change ¬0 < I; exact h.right
    · change ¬I < 0; exact h.left

-- maybe we want trichotomy wrt 0 (later on)

def midpoint : Dyadic := half (I.left + I.right)
-- def magnitude : Dyadic := (max (abs (I.left.toRat)) (abs (I.right.toRat))).toDyadic _

@[simp, grind] theorem left_le_midpoint : I.left ≤ I.midpoint := by
  simp only [le_iff_toRat, midpoint, toRat_half]
  field_simp
  rw [mul_two, toRat_add]
  exact add_le_add (by rfl) (I.isValid_toRat)

@[simp, grind] theorem midpoint_le_right : I.midpoint ≤ I.right := by
  simp only [le_iff_toRat, midpoint, toRat_half]
  field_simp
  rw [two_mul, toRat_add]
  apply add_le_add (I.isValid_toRat) (by rfl)

@[simp, grind] theorem midpoint_mem : ↑I.midpoint.toRat ∈ I := by
  simp only [mem_iff_mem_Icc, Set.mem_Icc, Rat.cast_le]
  grind only [left_le_midpoint, midpoint_le_right, le_iff_toRat]

def add : DyadicInterval :=
  let l := I.left + J.left
  let r := I.right + J.right
  have h : l ≤ r := add_le_add' I.isValid J.isValid
  ⟨l, r, h⟩

instance : Add DyadicInterval := ⟨DyadicInterval.add⟩

@[simp, grind] lemma left_add_eq : (I + J).left = I.left + J.left := by rfl

@[simp, grind] lemma right_add_eq : (I + J).right = I.right + J.right := by rfl

def neg (I : DyadicInterval) : DyadicInterval :=
  have h : -I.right ≤ -I.left := by
     simp only [le_iff_toRat, toRat_neg, neg_le_neg_iff, I.isValid_toRat]
  ⟨-I.right, -I.left, h⟩

instance : Neg DyadicInterval := ⟨DyadicInterval.neg⟩

@[simp, grind] lemma neg_left : (- I).left = -I.right := by rfl

@[simp, grind] lemma neg_right : (-I).right = -I.left := by rfl

def sub : DyadicInterval := I + (-J)

instance : Sub DyadicInterval where sub := DyadicInterval.sub

@[simp, grind] lemma sub_eq_neg_add : I - J = I + (-J) := by rfl

@[simp, grind] lemma left_sub_eq : (I - J).left = I.left - J.right := by
  simp only [sub_eq_neg_add, left_add_eq, neg_left, Dyadic.sub_eq_add_neg]

@[simp, grind] lemma right_sub_eq : (I - J).right = I.right - J.left := by
  simp only [sub_eq_neg_add, right_add_eq, neg_right, Dyadic.sub_eq_add_neg]

section Multiplication
open Finset
def productEndpts : Finset Dyadic :=
  {(I.left * J.left),
  (I.left * J.right),
  (I.right * J.left),
  (I.right * J.right)}

@[simp, grind] lemma product_endpts_nonempty : (productEndpts I J).Nonempty := by
  unfold productEndpts
  exact insert_nonempty (I.left * J.left) {I.left * J.right, I.right * J.left, I.right * J.right}

@[simp, grind] lemma product_endpts_comm : productEndpts I J = productEndpts J I := by
  simp only [productEndpts, Dyadic.mul_comm]
  grind only [= Set.mem_singleton_iff, = mem_singleton, = insert_eq_of_mem, = mem_insert, cases Or]

def mul : DyadicInterval :=
  let s := productEndpts I J
  have hs := product_endpts_nonempty I J
  ⟨min' s hs, max' s hs, min'_le_max' s hs⟩

instance : Mul DyadicInterval := ⟨DyadicInterval.mul⟩

@[simp, grind] lemma mul_left_endpt : (I * J).left =
  (productEndpts I J).min' (product_endpts_nonempty I J) := by rfl

@[simp, grind] lemma mul_right_endpt : (I * J).right =
  (productEndpts I J).max' (product_endpts_nonempty I J) := by rfl

@[simp, grind] lemma mul_left_mem_product_endpts : (I * J).left ∈ productEndpts I J := by
  simp only [mul_left_endpt, min'_mem]

@[simp, grind] lemma mul_right_mem_product_endpts : (I * J).right ∈ productEndpts I J := by
  simp only [mul_right_endpt, max'_mem]
end Multiplication

def powOdd (n : ℕ) (hn : n % 2 = 1) : DyadicInterval :=
  have h : I.left ^ n ≤ I.right ^ n := by
    simp only [le_iff_toRat, toRat_pow]
    rw [Odd.pow_le_pow]
    · exact I.isValid_toRat
    · rw [Nat.odd_iff]
      exact hn
  ⟨(I.left ^ n), (I.right ^ n), h⟩

def powEven (n : ℕ) (hn : n % 2 = 0) : DyadicInterval :=
  let r := max (I.left ^ n) (I.right ^ n)
  let l := min (I.left ^ n) (I.right ^ n)
  let l' := if I.left ≤ 0 ∧ 0 ≤ I.right then 0 else l
  have h : l' ≤ r := by
    rw [← Nat.even_iff] at hn
    unfold l' r l
    split_ifs
    · apply le_max_of_le_left
      rw [le_iff_toRat, toRat_zero, toRat_pow]
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

section M2
open Finset
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

@[simp, grind]
lemma product_endpts_zero : productEndpts I 0 = {0} := by
  simp only [productEndpts, left_coe_zero, right_coe_zero]
  simp only [Dyadic.mul_zero, mem_singleton, insert_eq_of_mem]

@[simp, grind]
lemma product_endpts_one : productEndpts I 1 = {I.left, I.right} := by
  have h₁ : left 1 = 1 := by rfl
  have h₂ : right 1 = 1 := by rfl
  simp only [productEndpts, h₁, h₂, Dyadic.mul_one]
  simp only [mem_singleton, insert_eq_of_mem, mem_insert, true_or]

@[simp, grind]
theorem add_comm : I + J = J + I := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_comm, and_self]

@[simp, grind]
theorem add_assoc : (I + J) + K = I + (J + K) := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_assoc, and_self]

@[simp, grind]
theorem zero_add : I + 0 = I := by
  rw [eq_iff_left_right, left_add_eq, right_add_eq]
  constructor
  · rw [left_coe_zero, Dyadic.add_zero]
  · rw [right_coe_zero, Dyadic.add_zero]

@[simp, grind]
theorem add_zero : 0 + I = I := by
  rw [add_comm, zero_add]

@[simp, grind]
theorem mul_comm : I * J = J * I := by
  simp only [eq_iff_left_right, mul_left_endpt, mul_right_endpt, product_endpts_comm, and_self]

@[simp, grind]
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

@[simp, grind]
theorem mul_zero : I * 0 = 0 := by
  simp only [eq_iff_left_right, mul_left_endpt, product_endpts_zero, min'_singleton, left_coe_zero,
    mul_right_endpt, max'_singleton, right_coe_zero, and_self]

@[simp, grind]
theorem zero_mul : 0 * I = 0 := by rw [mul_comm, mul_zero]

@[simp, grind]
theorem mul_one : I * 1 = I := by
  simp only [eq_iff_left_right, mul_left_endpt, product_endpts_one, mul_right_endpt]
  constructor
  · simp only [min'_eq_iff, mem_insert, mem_singleton, true_or, forall_eq_or_imp, le_refl, forall_eq, true_and, I.isValid]
  · simp only [max'_eq_iff, mem_insert, mem_singleton, or_true, forall_eq_or_imp, forall_eq, le_refl, and_true, I.isValid]
end M2
@[simp, grind]
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
        rw [← toRat_zero, ← le_iff_toRat]
        grind only
      have h₂ : x ^ n ≤ ((I.right ^ n).toRat : ℝ) := by
        rw [toRat_pow, Rat.cast_pow]
        apply pow_le_pow_left₀ _ hx.right
        apply le_trans _ hx.left
        norm_cast
        rw [← toRat_zero, ← le_iff_toRat]
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
          rw [← toRat_zero, ← toRat_neg, ← le_iff_toRat]
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
    apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
    simp only [Set.mem_Icc, hz, and_self]

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
        rw [← le_iff_toRat]
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
        rw [← toRat_zero, ← le_iff_toRat, ← le_iff_toRat]
        exact hI
      · simp only [pow_eq_zero_iff', ne_eq, true_and]
        exact hn'

    have h : z ∈ Image := by
      apply Set.mem_of_subset_of_mem
      apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
      simp only [Set.mem_Icc, hz, and_self]

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
      apply IsPreconnected.Icc_subset h₂.isPreconnected h₃ h₄
      simp only [Set.mem_Icc, hz, and_self]

    rcases h with ⟨x, hx, hx'⟩
    use x, hx, hx'

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
      have hn' : n + 1 ≠ 0 := by grind only
      obtain ⟨x, hx⟩ := powEven_sharp I (n + 1) hn hn' z hz
      grind only
    -- (n + 1) is odd
    · rename_i n' n hn
      obtain ⟨x, hx⟩ := powOdd_sharp I (n + 1) hn z hz
      grind only
    -- unreachable
    · grind only

-- Exactness of Operations
section Exactness
open Set

theorem add_exact : (I + J : Set ℝ) = image2 (· + ·) I J := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := add_sharp I J z hz
    exact mem_image2_of_mem hx hy
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact add_sound I J x hx y hy

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

theorem mul_exact : (I * J : Set ℝ) = image2 (· * ·) I J := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mul_sharp I J z hz
    exact mem_image2_of_mem hx hy
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_sound I J x hx y hy

theorem pow_exact : ↑(I^n) = (fun x ↦ x ^ n) '' (I : Set ℝ) := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := pow_sharp I n z hz
    exact mem_image_of_mem _ hx
  · rintro _ ⟨x, hx, rfl⟩
    exact pow_sound I n x hx

@[simp, grind]
theorem mul_assoc' : (I * J) * K = I * (J * K) := by
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

-- Distributivity doesn't hold in either direction. Choose counterexamples
end Exactness

section inclusion_isotonicity
open Set
variable {A B : DyadicInterval}

theorem add_isotonic (hI : I ⊆ A) (hJ : J ⊆ B) : I + J ⊆ A + B := by
  simp only [subset_iff, add_exact, image2_add]
  exact add_subset_add ((subset_iff I A).mp hI) ((subset_iff J B).mp hJ)

theorem neg_isotonic (hI : I ⊆ A) : -I ⊆ - A := by
  simp only [subset_iff, neg_exact, image_neg_eq_neg, neg_subset_neg]
  rw [← subset_iff]; exact hI

theorem sub_isotonic (hI : I ⊆ A) (hJ : J ⊆ B) : I - J ⊆ A - B := by
  simp only [subset_iff, sub_exact, image2_sub]
  exact sub_subset_sub ((subset_iff I A).mp hI) ((subset_iff J B).mp hJ)

theorem mul_isotonic (hI : I ⊆ A) (hJ : J ⊆ B) : I * J ⊆ A * B := by
  simp only [subset_iff, mul_exact, image2_mul]
  exact mul_subset_mul ((subset_iff I A).mp hI) ((subset_iff J B).mp hJ)

theorem pow_isotonic (hI : I ⊆ A) : I ^ n ⊆ A ^ n := by
  simp only [subset_iff, pow_exact]
  apply image_mono
  exact (subset_iff I A).mp hI

end inclusion_isotonicity

def intersection : Option DyadicInterval :=
  let l := max I.left J.left
  let r := min I.right J.right
  if h : l ≤ r then
    some {left := l, right := r, isValid := h}
  else none

infixl:70 " ⊓ " => intersection

theorem inter_self : I ⊓ I = some I := by
  simp only [intersection, max_self, min_self,
    Option.dite_none_right_eq_some, exists_prop, and_true, I.isValid]

theorem inter_comm (h : I ⊓ J = some K) : I ⊓ J = J ⊓ I := by
  simp only [intersection, max_comm, min_comm]

theorem inter_subset (h : J ⊆ I) : I ⊓ J = some J := by
  simp only [intersection, le_inf_iff, sup_le_iff, Option.dite_none_right_eq_some,
    Option.some.injEq, eq_iff_left_right, sup_eq_right, inf_eq_right, exists_and_left, exists_prop, I.isValid, J.isValid, and_true, true_and]
  grind only [eq_iff_left_right, left_le_midpoint,
    = Set.subset_def, sub_eq_neg_add, subset_refl, midpoint_le_right, mem_iff_mem_Icc, right_add_eq,
    right_sub_eq, subset_trans, Dyadic.sub_eq_add_neg, right_mem, left_sub_eq, isValid_toRat,
    left_mem, left_add_eq, midpoint_mem, isValid', subset_iff_endpts, cases Or]

theorem inter_subset_left (h : I ⊓ J = some K) : K ⊆ I := by
  simp only [intersection] at h
  simp only [le_inf_iff, sup_le_iff, Option.dite_none_right_eq_some, Option.some.injEq,
    eq_iff_left_right, exists_and_left, exists_prop, I.isValid, J.isValid, true_and, and_true] at h
  have h₁ := h.left
  have h₂ := h.right.left
  have h₃ := h.right.right
  clear h
  rw [subset_iff_endpts, ← h₁, ← h₃]
  simp only [le_max_left, min_le_left, and_self]

theorem inter_subset_right (h : I ⊓ J = some K) : K ⊆ J := by
  rw [inter_comm I J K h] at h
  exact inter_subset_left J I K h

theorem inter_optimal (X : DyadicInterval) (hI : X ⊆ I) (hJ : X ⊆ J) : ∃ K, I ⊓ J = some K ∧ X ⊆ K := by
  rw [subset_iff] at *
  have h := Set.subset_inter hI hJ
  clear hI hJ
  simp only [toSet, Set.Icc_inter_Icc] at h
  rw [Set.Icc_subset_Icc_iff X.isValid'] at h
  norm_cast at h
  simp only [← toRat_max, ← toRat_min, ← le_iff_toRat] at h
  have hK := le_trans h.left (le_trans X.isValid h.right)
  use ⟨max I.left J.left, min I.right J.right, hK⟩
  simp only [intersection, hK, Option.dite_none_right_eq_some, exists_prop,
    subset_iff, and_self, true_and, toSet, Set.Icc_subset_Icc_iff X.isValid']
  norm_cast
  simp only [← le_iff_toRat, h, and_self]

theorem inter_toSet_some (h : I ⊓ J = some K) : (I : Set ℝ) ∩ ↑J = ↑K := by
  apply subset_antisymm
  · intro z hz
    unfold toSet at *
    simp only [intersection, le_inf_iff, sup_le_iff, Option.dite_none_right_eq_some, Option.some.injEq,
      eq_iff_left_right, exists_and_left, exists_prop] at h
    simp only [Set.Icc_inter_Icc, Set.mem_Icc,
      ← Rat.cast_max, ← toRat_max, h.left, ← Rat.cast_min, ← toRat_min, h.right.right] at hz
    simp only [Set.mem_Icc, hz, and_true]
  · intro z hz
    unfold toSet at *
    simp only [intersection, le_inf_iff, sup_le_iff, Option.dite_none_right_eq_some, Option.some.injEq,
      eq_iff_left_right, exists_and_left, exists_prop] at h
    simp only [Set.mem_Icc] at hz
    simp only [Set.Icc_inter_Icc, Set.mem_Icc, ← Rat.cast_max, ← toRat_max, h.left, ← Rat.cast_min, ← toRat_min, h.right.right, hz, and_true]

theorem inter_toSet_none (h : I ⊓ J = none) : (I : Set ℝ) ∩ ↑J = ∅ := by
  simp only [intersection, dite_eq_right_iff, reduceCtorEq] at h
  rw [Set.eq_empty_iff_forall_notMem]
  intro x h'
  simp only [toSet] at h'
  simp only [Set.Icc_inter_Icc, Set.mem_Icc, ← Rat.cast_max, ← toRat_max, ← Rat.cast_min, ← toRat_min] at h'
  have h' := le_trans h'.left h'.right
  norm_cast at h'
  rw [← le_iff_toRat] at h'
  exact h h'

def hull : DyadicInterval :=
  let l := min I.left J.left
  let r := max I.right J.right
  have h : l ≤ r := by
    apply le_trans (min_le_left I.left J.left)
    apply le_trans _ (le_max_left I.right J.right)
    exact I.isValid
  ⟨l, r, h⟩

infixl:65 " ⊔ " => hull

theorem hull_self : I ⊔ I = I := by simp only [hull, min_self, max_self]

theorem hull_comm : I ⊔ J = J ⊔ I := by grind only [hull]

theorem hull_subset (h : I ⊆ J) : I ⊔ J = J := by
  simp only [subset_iff_endpts] at h
  simp only [hull, eq_iff_left_right, inf_eq_right, sup_eq_right, h, and_self]

theorem left_subset_hull : I ⊆ I ⊔ J := by
  simp only [hull, subset_iff_endpts, min_le_left, le_max_left, and_self]

theorem right_subset_hull : J ⊆ I ⊔ J := by grind only [hull_comm, left_subset_hull]

theorem hull_optimal (X : DyadicInterval) (hI : I ⊆ X) (hJ : J ⊆ X) : I ⊔ J ⊆ X := by
  simp only [hull, subset_iff_endpts] at *
  simp only [le_min_iff, max_le_iff, hI, hJ, and_self]

def split : DyadicInterval × DyadicInterval :=
  let left_half : DyadicInterval := ⟨I.left, I.midpoint, I.left_le_midpoint⟩
  let right_half : DyadicInterval := ⟨I.midpoint, I.right, I.midpoint_le_right⟩
  (left_half, right_half)

theorem left_split_subset : I.split.1 ⊆ I := by
  simp only [split, subset_iff_endpts, le_refl, midpoint_le_right, and_self]

theorem right_split_subset : I.split.2 ⊆ I := by
  simp only [split, subset_iff_endpts, le_refl, left_le_midpoint, and_self]

theorem split_hull : I.split.1 ⊔ I.split.2 = I := by
  simp only [split, hull, eq_iff_left_right]
  exact ⟨min_eq_left I.left_le_midpoint, max_eq_right I.midpoint_le_right⟩

theorem split_inter : I.split.1 ⊓ I.split.2 = some ↑I.midpoint := by
  simp only [intersection, split, left_le_midpoint, sup_of_le_right, midpoint_le_right,
    inf_of_le_left, le_refl, ↓reduceDIte, ofDyadic]

theorem mem_split_iff : ∀ x ∈ I, x ∈ I.split.1 ∨ x ∈ I.split.2 := by
  intro x hx
  simp only [mem_iff_le_endpts] at *
  rcases le_total x ↑I.midpoint.toRat with h₁ | h₂
  · left; simp only [split]; exact ⟨hx.left, h₁⟩
  · right; simp only [split];  exact ⟨h₂, hx.right⟩

theorem split_width : I.split.1.width = half I.width := by
  simp only [split, width, midpoint, toRat_eq, toRat_sub, toRat_half, toRat_add]
  linarith

theorem split_width_right : I.split.2.width = half I.width := by
  simp only [split, width, midpoint, toRat_eq, toRat_sub, toRat_half, toRat_add]
  linarith

section PolynomialBounds
open Vector Polynomial
abbrev RatPol (n : ℕ) := Vector ℚ n -- degree ≤ n-1

noncomputable def toPoly {n : ℕ} (p : RatPol n) : Polynomial ℚ := Polynomial.ofFn n p.get

noncomputable def toRealPoly {n : ℕ} (p : RatPol n) : Polynomial ℝ := (toPoly p).map (algebraMap ℚ ℝ)

lemma to_poly_trivial (p : RatPol 0) : (toPoly p) = 0 := by
  simp only [toPoly]; apply Polynomial.ext
  grind only [Polynomial.coeff_zero, Polynomial.ofFn_coeff_eq_zero_of_ge]

lemma to_real_poly_trivial (p : RatPol 0) : (toRealPoly p) = 0 := by
  simp only [toRealPoly]
  rw [Polynomial.map_eq_zero_iff]
  · exact to_poly_trivial p
  · exact Rat.cast_injective

lemma to_poly_coeff {n : ℕ} (p : RatPol n) (k : ℕ) :
  (toPoly p).coeff k = if h : k < n then (p.get ⟨k,h⟩) else 0 := by
  unfold toPoly
  split_ifs with h
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ h]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by grind only)]

lemma to_real_poly_coeff {n : ℕ} (p : RatPol n) (k : ℕ) :
  (toRealPoly p).coeff k =
    if h : k < n then ↑(p.get ⟨k,h⟩) else 0 := by
    unfold toRealPoly
    simp only [Polynomial.coeff_map, to_poly_coeff]
    simp only [eq_ratCast]
    split_ifs with h
    · norm_cast
    · norm_cast

def firstNonzeroCoeff {n : ℕ} (p : RatPol n) := p.tail.toList.find? (fun x ↦ x ≠ 0)
def firstNonzeroIdx {n : ℕ} (p : RatPol n) := p.tail.toList.findIdx? (fun x ↦ x ≠ 0)

lemma firstNonzeroIdx_lt {m : ℕ} {k : ℕ} (p : RatPol (m +1)) : firstNonzeroIdx p = some k → k < m := by
  intro hk; unfold firstNonzeroIdx at hk
  rw [List.findIdx?_eq_some_iff_getElem] at hk
  simp only [Nat.add_one_sub_one, tail_eq_cast_extract, getElem_toList, getElem_cast,
    getElem_extract, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Decidable.not_not, length_toList] at hk
  grind only

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

theorem countP_eq_one_tail_get
  {m : ℕ} {a : ℚ} {k : ℕ} (p : RatPol (m+1)) (hcoeff : firstNonzeroCoeff p = some a)
  (hidx : firstNonzeroIdx p = some k) (heq : p.tail.countP (fun x ↦ decide (x ≠ 0)) = 1) :
  ∀ i : Fin m, p.tail.get i = if (i.val = k) then a else 0 := by
  grind only [countP_eq_one_tail_get_nonzero, countP_eq_one_tail_get_zero]


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


def deriv {n : ℕ} (p : RatPol n) := p.tail.mapIdx (fun i c => c * ((i : ℚ) + 1))

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

theorem deriv_eq_real_poly_deriv {n : ℕ} (p : RatPol n) :
  toRealPoly (deriv p) = (toRealPoly p).derivative := by
  simp only [toRealPoly, Polynomial.derivative_map, deriv_eq_poly_deriv]

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
            exact le_iff_toRat.mp I.midpoint_le_right
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
            exact le_iff_toRat.mp I.left_le_midpoint
          · grind only
        · grind only

-- Horner's method => This will actually be used in computation
-- But still consider not using foldr, and using direct evaluation
#check Fin.sum_univ_eq_sum_range
#check Finset.sum_fin_eq_sum_range
def evalWithPrec {n : ℕ} (prec : ℤ) (p : RatPol n) (x : ℚ) : DyadicInterval :=
  -- let px := p.foldr (fun coeff acc ↦ coeff + x * acc) 0
  let px := ∑ i : Fin n, (p.get i) * x ^ (i : ℕ)
  ofRatWithPrec prec px

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

theorem eval_sound {n : ℕ} (prec : ℤ) (p : RatPol n) (x : ℚ) :
  (toRealPoly p).eval ↑x ∈ evalWithPrec prec p x := by
  unfold evalWithPrec
  rw [eval_to_real_poly prec]
  apply rat_mem_of_rat

-- def eval' {n : ℕ} (p : RatPol n) (z : ℝ) : ℝ := p.foldr (fun coeff acc ↦ ↑coeff + z * acc) 0
-- theorem eval_eq_poly_eval {n : ℕ} (p : RatPol n) (z : ℝ) : eval' p z = (toPoly p).aeval z := by sorry

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

theorem const_to_real_poly {m : ℕ} (p : RatPol (m +1)) (hp : p.tail.countP (· ≠ 0) = 0) :
  toRealPoly p = Polynomial.C ↑p.head := by
  unfold toRealPoly
  rw [const_to_poly _ hp]
  simp only [map_C, eq_ratCast]

def intervalEvalWithPrec {n : ℕ} (prec : ℤ) (p : RatPol n) (I : DyadicInterval) : DyadicInterval :=
  match n with
  | 0 => 0
  | m + 1 =>
    match p.tail.countP (· ≠ 0) with
    | 0 => ofRatWithPrec prec p.head -- Constant Polynomial
    | 1 => -- Constant + Monomial
      let a := firstNonzeroCoeff p
      let k := firstNonzeroIdx p
      match a, k with
      | some a, some k =>  ofRatWithPrec prec p.head + (ofRatWithPrec prec a) * I ^ (k + 1)
      | _, _ => 0 -- Unreachable
    | _ => --Centered form
      (evalWithPrec prec p I.midpoint.toRat) + (intervalEvalWithPrec prec (deriv p) I) * (I - I.midpoint)
    -- p(m) + p'(I) * (I - c)

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
      rw [h, add_comm]
      apply add_sound
      · apply mul_sound
        · apply interval_eval_sound
          exact hc
        · apply sub_sound
          · exact hx
          · simp only [ofDyadic, mem_iff_le_endpts, le_refl, and_self]
      · apply eval_sound

-- Notoriously hard to prove!?
-- theorem eval_isotonic {n : ℕ} (p : RatPol n) (prec : ℤ) :
--   I ⊆ J → intervalEvalWithPrec prec p I ⊆ intervalEvalWithPrec prec p J := by sorry

end PolynomialBounds
end
end DyadicInterval

open DyadicInterval
def empty : Vector ℚ 0 := ⟨#[], rfl⟩
def I : DyadicInterval := ⟨2, 3, rfl⟩
def J : DyadicInterval := ofRatWithPrec 5 ((7:ℚ)/9)
def p : Vector ℚ 4 := ⟨#[3, 5, 9/7, 1], rfl⟩
#eval deriv p
#eval evalWithPrec 5 p 1
#check HMul
/-
I ⊆ J
I ⊆ A, J ⊆ B → I op J ⊆ A op B
I * (J + K) ⊆ I * J + I * K
∀ x ∈ I, p(x) ∈ p(I)
-/
