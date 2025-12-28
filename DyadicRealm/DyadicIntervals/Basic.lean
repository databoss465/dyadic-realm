import Mathlib
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false

/-!
# Dyadic Intervals

Constructs non-empty dyadic intervals from its endpoints.

## Main Definitions

* `DyadicInterval`: A structure wrapping two Dyadic numbers `left`, `right` and `left ≤ right`.
* `midpoint`: The arithmetic mean of the endpoints.
* `width`: The length of the interval ($right - left$).
* `ofRatWithPrec`: Approximates a rational number into a `DyadicInterval` with a given precision.
* `toSet` : coerces a `DyadicInterval` to the corresponding `Set ℝ`
* `HasZero`: A decidable predicate indicating the interval contains 0.
* `ZeroFree`: A decidable predicate indicating the interval strictly excludes 0 (useful for division safety).
* `intersection` : Intersection of `DyadicInterval` as `Option DyadicInterval`
* `hull` : The hull of two interval
* `split` : Splits an interval at the midpoint

-/

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
section DyadicAddendum
open Dyadic Finset

def format (d : Dyadic) : String :=
  if (d.toRat).den == 1 then
    toString (d.toRat).num  -- Print "5" instead of "5/1"
  else
    s!"{(d.toRat).num}/{(d.toRat).den}"

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

theorem toRat_half {a : Dyadic} : (half a).toRat = a.toRat/2 := by
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

end DyadicAddendum
end Dyadic

-- Define Dyadic Intervals as left and right endpoints with a proof that left ≤ right
structure DyadicInterval where
  left : Dyadic
  right : Dyadic
  isValid : left ≤ right
  deriving DecidableEq

instance : Repr DyadicInterval where
  reprPrec I _ := s!"[{Dyadic.format I.left}, {Dyadic.format I.right}]"

namespace DyadicInterval
section DI_Structural
open Dyadic
variable (I J K : DyadicInterval)(a : Dyadic)(n : ℕ)

@[simp, grind] theorem eq_iff_left_right : I = J ↔ I.left = J.left ∧ I.right = J.right := by
  constructor
  · grind only
  · intro h; cases I; cases J
    grind only

@[simp, grind] theorem isValid_toRat : I.left.toRat ≤ I.right.toRat := by
  simp only [← le_iff_toRat, I.isValid]

@[simp, grind] theorem isValid' : (I.left.toRat : ℝ) ≤ I.right.toRat := by
  simp only [Rat.cast_le, isValid_toRat]

/-- Converts a dyadic into a degenerate interval -/
def ofDyadic : DyadicInterval := ⟨a, a, le_rfl⟩
instance : Coe Dyadic DyadicInterval := ⟨DyadicInterval.ofDyadic⟩

instance (n : Nat) : OfNat DyadicInterval n :=
  ⟨((n : Dyadic) : DyadicInterval)⟩

instance : NatCast DyadicInterval :=
  ⟨fun n => ((n : Dyadic) : DyadicInterval)⟩

instance : IntCast DyadicInterval :=
  ⟨fun z => ((z : Dyadic) : DyadicInterval)⟩

/-- Converts a rational to a dyadic interval with endpoints at the given precision -/
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

@[simp, grind] lemma left_coe : (a : DyadicInterval).left = a := by rfl

@[simp, grind] lemma right_coe : (a : DyadicInterval).right = a := by rfl

#check left_coe 0 -- left_coe 0 : (ofDyadic 0).left = 0
-- These are written separately to handle some typeclass stuff
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

/-- Real sets corresponding to `DyadicInterval` are nonempty -/
theorem nonempty : Nonempty (I : Set ℝ) := ⟨↑I.left.toRat, I.left_mem⟩

/-- `DyadicInterval`s are equal if Real intervals corresponding to them are equal -/
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

/-- `DyadicInterval` contains zero iff it is between the endpoints -/
@[simp, grind] theorem haszero_iff : HasZero I ↔ I.left ≤ 0 ∧ 0 ≤ I.right := by
  constructor
  · intro h; exact h.p
  · intro h; exact ⟨h⟩

@[simp, grind] theorem haszero_iff_mem_zero : HasZero I ↔ 0 ∈ I := by
  simp only [mem_iff_le_endpts, haszero_iff]; norm_cast
  simp only [le_iff_toRat, toRat_zero]

/-- Dyadic interval has zero iff if it is not zero free -/
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

@[simp, grind] theorem zerofree_iff_not_mem_zero : ZeroFree I ↔ 0 ∉ I := by
  rw [← (haszero_iff_not_zerofree I).not_left, haszero_iff_mem_zero]

-- maybe we want trichotomy wrt 0 (later on)
-- ∀ I : DyadicInterval, 0 ∈ I ∨ (0 < I ∨ I < 0)

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

end DI_Structural

section DI_Topological
open Dyadic Set
variable (I J K : DyadicInterval)(a : Dyadic)(n : ℕ)

def subset : Prop := J.left ≤ I.left ∧ I.right ≤ J.right
instance : HasSubset DyadicInterval := ⟨DyadicInterval.subset⟩
instance : HasSSubset DyadicInterval where SSubset I J := I ⊆ J ∧ I ≠ J

@[simp, grind] theorem subset_iff : I ⊆ J ↔ I.toSet ⊆ J.toSet := by
  simp only [toSet]
  rw [Set.Icc_subset_Icc_iff I.isValid']
  simp only [Rat.cast_le, ← le_iff_toRat]; rfl

@[simp, grind] theorem subset_iff_endpts : I ⊆ J ↔ J.left ≤ I.left ∧ I.right ≤ J.right := by rfl

@[simp, grind] theorem ssubset_iff : I ⊂ J ↔ I ⊆ J ∧ I ≠ J := by rfl

/-- Width of a subset is at most the width of the superset -/
theorem subset_width : I ⊆ J → I.width ≤ J.width := by
  grind only [subset_iff_endpts, width, le_iff_toRat]

/-- If a subset has equal width then it is equal to the superset -/
theorem subset_and_eq_width : I ⊆ J → I.width = J.width → I = J := by
  grind only [subset_iff_endpts, width, = Set.mem_Icc, eq_iff_left_right, isValid_toRat, isValid']

/-- Width of a strict subset is strictly less than the width of the superset -/
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

def intersection : Option DyadicInterval :=
  let l := max I.left J.left
  let r := min I.right J.right
  if h : l ≤ r then
    some {left := l, right := r, isValid := h}
  else none

infixl:70 " ⊓ " => intersection

/-- Intersection with itself gives the same interval -/
theorem inter_self : I ⊓ I = some I := by
  simp only [intersection, max_self, min_self,
    Option.dite_none_right_eq_some, exists_prop, and_true, I.isValid]

/-- Intersection is commutative -/
theorem inter_comm : I ⊓ J = J ⊓ I := by
  simp only [intersection, max_comm, min_comm]

/-- If one interval is a subset of the other, the intersection is the smaller interval -/
theorem inter_subset (h : J ⊆ I) : I ⊓ J = some J := by
  simp only [intersection, le_inf_iff, sup_le_iff, Option.dite_none_right_eq_some,
    Option.some.injEq, eq_iff_left_right, sup_eq_right, inf_eq_right, exists_and_left, exists_prop, I.isValid, J.isValid, and_true, true_and]
  grind only [eq_iff_left_right, left_le_midpoint, sub_eq_neg_add, subset_refl, midpoint_le_right, mem_iff_mem_Icc, subset_trans, Dyadic.sub_eq_add_neg, right_mem, isValid_toRat,
    left_mem, midpoint_mem, isValid', subset_iff_endpts, cases Or]

/-- The intersection is a subset of the left interval -/
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

/-- The intersection is a subset of the right interval -/
theorem inter_subset_right (h : I ⊓ J = some K) : K ⊆ J := by
  rw [inter_comm I J] at h
  exact inter_subset_left J I K h

/-- The intersection is the largest interval contained in both intervals -/
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

/-- Set corresponding to the nonempty intersection of `DyadicInterval`s is the intersection of corresponding sets -/
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

/-- If the intersection is empty, then the corresponding sets have empty intersection -/
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

/-- Hull with itself gives the same interval -/
theorem hull_self : I ⊔ I = I := by simp only [hull, min_self, max_self]

/-- Hull is commutative -/
theorem hull_comm : I ⊔ J = J ⊔ I := by grind only [hull]

/-- If one interval is a superset of the other, the hull is the larger interval -/
theorem hull_subset (h : I ⊆ J) : I ⊔ J = J := by
  simp only [subset_iff_endpts] at h
  simp only [hull, eq_iff_left_right, inf_eq_right, sup_eq_right, h, and_self]

/-- The left interval is a subset of the hull -/
theorem left_subset_hull : I ⊆ I ⊔ J := by
  simp only [hull, subset_iff_endpts, min_le_left, le_max_left, and_self]

/-- The right interval is a subset of the hull -/
theorem right_subset_hull : J ⊆ I ⊔ J := by grind only [hull_comm, left_subset_hull]

/-- The hull is the smallest interval containing both intervals -/
theorem hull_optimal (X : DyadicInterval) (hI : I ⊆ X) (hJ : J ⊆ X) : I ⊔ J ⊆ X := by
  simp only [hull, subset_iff_endpts] at *
  simp only [le_min_iff, max_le_iff, hI, hJ, and_self]

/-- Splits the interval at the midpoint -/
def split : DyadicInterval × DyadicInterval :=
  let left_half : DyadicInterval := ⟨I.left, I.midpoint, I.left_le_midpoint⟩
  let right_half : DyadicInterval := ⟨I.midpoint, I.right, I.midpoint_le_right⟩
  (left_half, right_half)

/-- The left split is a subset of the original interval -/
theorem left_split_subset : I.split.1 ⊆ I := by
  simp only [split, subset_iff_endpts, le_refl, midpoint_le_right, and_self]

/-- The right split is a subset of the original interval -/
theorem right_split_subset : I.split.2 ⊆ I := by
  simp only [split, subset_iff_endpts, le_refl, left_le_midpoint, and_self]

/-- The hull of the splits is the original interval -/
theorem split_hull : I.split.1 ⊔ I.split.2 = I := by
  simp only [split, hull, eq_iff_left_right]
  exact ⟨min_eq_left I.left_le_midpoint, max_eq_right I.midpoint_le_right⟩

/-- The intersection of the splits is the degenerate interval at the midpoint -/
theorem split_inter : I.split.1 ⊓ I.split.2 = some ↑I.midpoint := by
  simp only [intersection, split, left_le_midpoint, sup_of_le_right, midpoint_le_right,
    inf_of_le_left, le_refl, ↓reduceDIte, ofDyadic]

/-- Any point in the interval is in one of the splits -/
theorem mem_split_iff : ∀ x ∈ I, x ∈ I.split.1 ∨ x ∈ I.split.2 := by
  intro x hx
  simp only [mem_iff_le_endpts] at *
  rcases le_total x ↑I.midpoint.toRat with h₁ | h₂
  · left; simp only [split]; exact ⟨hx.left, h₁⟩
  · right; simp only [split];  exact ⟨h₂, hx.right⟩

/-- Width of left split is half the width of the original interval -/
theorem split_width_left : I.split.1.width = half I.width := by
  simp only [split, width, midpoint, toRat_eq, toRat_sub, toRat_half, toRat_add]
  linarith

/-- Width of right split is half the width of the original interval -/
theorem split_width_right : I.split.2.width = half I.width := by
  simp only [split, width, midpoint, toRat_eq, toRat_sub, toRat_half, toRat_add]
  linarith

end DI_Topological
end DyadicInterval
