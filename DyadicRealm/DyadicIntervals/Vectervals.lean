import Mathlib
-- import LeanCert
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace Vector

theorem get_pop {α : Type} {n : ℕ} (v : Vector α (n + 1))(i : Fin n) :
  (v.pop).get i = v.get i.castSucc := by
  simp only [get, Nat.add_one_sub_one, pop, Fin.val_cast, Array.getElem_pop, getElem_toArray,
    Fin.val_castSucc]

theorem get_add {α : Type} {n : ℕ} [Add α] (xs ys : Vector α n) :
  (xs + ys).get = xs.get + ys.get := by
  change Vector.get (Vector.add xs ys) = Vector.get xs + Vector.get ys
  ext1 i; simp only [Vector.add, get_eq_getElem, getElem_zipWith, Pi.add_apply]

theorem get_sub {α : Type} {n : ℕ} [Sub α] (xs ys : Vector α n) :
  (xs - ys).get = xs.get - ys.get := by
  change Vector.get (Vector.sub xs ys) = Vector.get xs - Vector.get ys
  ext1 i; simp only [Vector.sub, get_eq_getElem, getElem_zipWith, Pi.sub_apply]

end Vector

abbrev Vecterval (n : ℕ) := Vector DyadicInterval n

namespace Vecterval

section VectervalStructural
open Dyadic DyadicInterval Set Vector
variable {n : ℕ} (X Y : Vecterval n)

def zero : Vecterval n := replicate _ 0
instance : Zero (Vecterval n) := ⟨zero⟩

lemma get_zero (i : Fin n): (0 : Vecterval n).get i = 0 := by
  change Vector.get (replicate n 0) i = 0
  simp only [get_replicate]

def one : Vecterval n := replicate _ 1
instance : One (Vecterval n) := ⟨one⟩

lemma get_one (i : Fin n) : (1 : Vecterval n).get i = 1 := by
  change Vector.get (replicate n 1) i = 1
  simp only [get_replicate]

def ofFn (f : Fin n → DyadicInterval) : Vecterval n := Vector.ofFn f

@[simp, grind =]
theorem get_ofFn (f : Fin n → DyadicInterval) (i : Fin n) :
  (Vecterval.ofFn f).get i = f i := Vector.get_ofFn f i

theorem getElem_ofFn (f : Fin n → DyadicInterval) (i : ℕ) (h : i < n):
  (Vecterval.ofFn f)[i] = f ⟨i, h⟩ := by simp only [Vecterval.ofFn, Vector.getElem_ofFn]

@[simp, grind =]
theorem ofFn_get_eq_self : Vecterval.ofFn X.get = X := by
  apply Vector.ext; intro i hi
  simp only [Vecterval.getElem_ofFn, get_eq_getElem]

@[simp, grind =]
theorem get_add : (X + Y).get = X.get + Y.get := by
  simp only [Vector.get_add]

@[simp, grind =]
theorem get_sub : (X - Y).get = X.get - Y.get := by
  simp only [Vector.get_sub]

@[simp]
theorem eq_empty {xs : Vecterval 0} : xs = #v[] := by simp only [Vector.eq_empty]

def mem (x : Vector ℝ n) := ∀ i : Fin n, x.get i ∈ X.get i
instance : Membership (Vector ℝ n) (Vecterval n) where mem := Vecterval.mem

def ofVecDyadic (V : Vector Dyadic n) : Vecterval n := V.map (fun a ↦ ofDyadic a)
instance : Coe (Vector Dyadic n) (Vecterval n) := ⟨Vecterval.ofVecDyadic⟩

def ofVecNat (V : Vector ℕ n) : Vecterval n := V.map (fun (m : ℕ)  ↦ (m : DyadicInterval))
instance : Coe (Vector ℕ n) (Vecterval n) := ⟨Vecterval.ofVecNat⟩

def ofVecInt (V : Vector ℤ n) : Vecterval n := V.map (fun (m : ℤ)  ↦ (m : DyadicInterval))
instance : Coe (Vector ℤ n) (Vecterval n) := ⟨Vecterval.ofVecInt⟩

def ofVecRatWithPrec (prec : ℤ) (V : Vector ℚ n) := V.map (ofRatWithPrec prec)

/-- Set of functions `f : Fin n → ℝ` such that for every coordinate `i`,
    `f i` lies in the interval `X.get i`. -/
def toSet := Set.pi Set.univ (fun i => (X.get i).toSet)

@[simp, grind .]
theorem nonempty : X.toSet.Nonempty := by
  simp [toSet, Set.univ_pi_nonempty_iff, DyadicInterval.nonempty]

theorem convex : Convex ℝ X.toSet := by
  apply convex_pi
  simp only [mem_univ, DyadicInterval.toSet, convex_Icc, imp_self, implies_true]

theorem compact : IsCompact X.toSet := by
  apply isCompact_univ_pi
  grind only [DyadicInterval.toSet, isCompact_Icc]

theorem complete : IsComplete X.toSet :=
  IsCompact.isComplete X.compact

@[simp, grind =]
theorem mem_iff (x : Vector ℝ n) : x ∈ X ↔ ∀ i : Fin n, x.get i ∈ X.get i := by rfl

@[simp, grind =]
theorem mem_iff_get_mem_toSet (x : Vector ℝ n) : x ∈ X ↔ x.get ∈ X.toSet := by
  simp only [mem_iff, toSet, mem_pi, mem_univ, forall_const]; rfl

theorem mem_iff_le_endpts (x : Vector ℝ n) :  x ∈ X ↔ ∀ i : Fin n,
  (X.get i).left.toRat ≤ x.get i ∧ x.get i ≤ (X.get i).right.toRat := by
  simp only [mem_iff, DyadicInterval.mem_iff_le_endpts]

theorem mem_pop_of_mem (X : Vecterval (n + 1))(x : Vector ℝ (n + 1)) :  x ∈ X → x.pop ∈ X.pop := by
  intro hx
  simp only [Vecterval.mem_iff, get_eq_getElem, getElem_pop] at *
  simp only [Nat.add_one_sub_one]; intro i
  exact hx (Fin.castSucc i)

theorem mem_back_of_mem (X : Vecterval (n + 1))(x : Vector ℝ (n + 1)) :  x ∈ X → x.back ∈ X.back := by
  intro hx
  simp only [back_eq_getElem, add_tsub_cancel_right]
  simp only [Vecterval.mem_iff, get_eq_getElem] at hx
  specialize hx ⟨n, by grind only⟩
  grind only

def midpoint : Vector Dyadic n := X.map (fun I ↦ I.midpoint)

def midpoint_rat {n : ℕ} (X : Vecterval n) : Vector ℚ n := X.midpoint.map toRat

def midpoint_real {n : ℕ} (X : Vecterval n) : Vector ℝ n := X.midpoint_rat.map (Rat.cast)

theorem midpoint_mem {n : ℕ} (X : Vecterval n) : X.midpoint_real ∈ X := by
  simp only [midpoint_real, midpoint_rat, midpoint, Vector.map_map, mem_iff, Vector.get_map, Function.comp_apply,
    DyadicInterval.midpoint_mem, implies_true]

def width : Vector Dyadic n := X.map (fun I ↦ I.width)

def maxWidth {n : ℕ} (X : Vecterval n) : Dyadic :=
  match n with
  | 0 => 0
  | m + 1 => max (X.back.width) (maxWidth X.pop)

def maxWidthIdx {n : ℕ} (X : Vecterval (n + 1)) : Fin (n + 1) :=
  match n with
  | 0 => 0
  | m + 1 =>
    let j : Fin (m + 1) := maxWidthIdx (X.pop)
    if maxWidth X.pop ≤ X.back.width then Fin.last (m + 1)
    else j.castSucc

def norm {n : ℕ} (X : Vecterval n) : Dyadic :=
  ∑ i : Fin n, (X.get i).abs

theorem norm_nonneg : 0 ≤ X.norm := by
  apply Finset.sum_nonneg
  grind only [DyadicInterval.abs_nonneg]

def norm' : NNReal where
  val := X.norm.toRat
  property := by
    simp only [Rat.cast_nonneg, ← toRat_zero, toRat_le_toRat_iff, norm_nonneg]

def dotProduct : DyadicInterval := X.get ⬝ᵥ Y.get
infixl:72 " ⬝ᵥ " => dotProduct

@[simp, grind =]
theorem dotProduct_comm : X ⬝ᵥ Y = Y ⬝ᵥ X := by simp only [dotProduct, _root_.dotProduct_comm]

@[simp, grind =]
lemma ofFn_mem_iff (f : Fin n → ℝ) : Vector.ofFn f ∈ X ↔ ∀ i, f i ∈ X.get i := by
  simp only [mem_iff, Vector.get_ofFn]

@[simp, grind =]
theorem mem_toSet_iff (f : Fin n → ℝ) : f ∈ X.toSet ↔ (Vector.ofFn f) ∈ X := by
  simp only [toSet, mem_pi, mem_univ, forall_const, mem_iff, Vector.get_ofFn]
  rfl

lemma sum_sound {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (F : ι → DyadicInterval)
  (h : ∀ i ∈ s, f i ∈ F i) : ∑ i ∈ s, f i ∈ ∑ i ∈ s, F i := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : 0 = (toRat 0 : ℝ) := by simp only [toRat_zero, Rat.cast_zero]
    change 0 ∈ ofDyadic 0
    rw [this]; apply to_rat_mem_of_dyadic
  | insert a s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    apply add_sound
    · apply h _ (Finset.mem_insert_self a s')
    · apply ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem dot_product_sound (x y : Fin n → ℝ) (hx : Vector.ofFn x ∈ X)
  (hy : Vector.ofFn y ∈ Y) : x ⬝ᵥ y ∈ X ⬝ᵥ Y := by
  unfold dotProduct _root_.dotProduct
  apply sum_sound
  simp only [Finset.mem_univ, forall_const]
  intro i; simp only [ofFn_mem_iff] at *
  apply mul_sound <;> grind only

@[grind .]
def lt : Prop := ∀ i, X.get i < Y.get i
instance : LT (Vecterval n) := ⟨Vecterval.lt⟩

@[simp, grind .] theorem lt_iff : X < Y ↔ ∀ i, X.get i < Y.get i := by rfl

class ZeroFree : Prop where p : ∃ i, (X.get i).ZeroFree
instance : Decidable (ZeroFree X) :=
  if h : ∃ i, (X.get i).ZeroFree then isTrue ⟨h⟩
  else isFalse (fun h_class => h h_class.p)

theorem zerofree_iff : ZeroFree X ↔ ∃ i, (X.get i).ZeroFree := by
  constructor <;> intro h
  · exact h.p
  · exact ⟨h⟩

theorem zerofree_iff_not_mem_zero : ZeroFree X ↔ 0 ∉ X := by
  simp only [zerofree_iff, DyadicInterval.zerofree_iff_not_mem_zero]
  simp only [mem_iff, not_forall]
  change (∃ i, 0 ∉ Vector.get X i) ↔ ∃ x, Vector.get (replicate n (0 : ℝ)) x ∉ Vector.get X x
  simp only [get_replicate]

theorem mem_zerofree_neq_zero : ZeroFree X → ∀ x ∈ X, x ≠ 0 := by
  grind only [zerofree_iff_not_mem_zero]

class HasZero : Prop where p : ∀ i, (X.get i).HasZero
instance : Decidable (HasZero X) :=
  if h : ∀ i, (X.get i).HasZero then isTrue ⟨h⟩
  else isFalse (fun h_class => h h_class.p)

theorem haszero_iff : HasZero X ↔ ∀ i, (X.get i).HasZero := by
  constructor <;> intro h
  · exact h.p
  · exact ⟨h⟩

theorem zerofree_iff_not_has_zero : ZeroFree X ↔ ¬ HasZero X := by
  grind only [zerofree_iff, haszero_iff, = zerofree_iff_not_haszero, haszero_or_zerofree, #b3c7,
    #cd2c, #3f47, #9f13]

theorem has_zero_iff_not_zerofree : HasZero X ↔ ¬ ZeroFree X := by grind only [zerofree_iff_not_has_zero]

theorem haszero_iff_mem_zero : HasZero X ↔ 0 ∈ X := by
  grind only [has_zero_iff_not_zerofree, zerofree_iff_not_mem_zero]

end VectervalStructural

section VectervalTopological
open Dyadic DyadicInterval Set Vector
variable {n : ℕ} (X Y Z: Vecterval n)

def subset := ∀ i : Fin n, X.get i ⊆ Y.get i
instance : HasSubset (Vecterval n) := ⟨Vecterval.subset⟩
instance : HasSSubset (Vecterval n) where SSubset X Y := X ⊆ Y ∧ X ≠ Y

@[simp, grind =]
theorem subset_iff : X ⊆ Y ↔ ∀ i : Fin n, X.get i ⊆ Y.get i := by rfl

@[simp, grind =]
theorem subset_iff_toSet : X ⊆ Y ↔ X.toSet ⊆ Y.toSet := by
  constructor
  · grind only [subset_iff, DyadicInterval.subset_iff, toSet, pi_subset_pi_iff, mem_univ]
  · intro h; simp only [toSet, pi_subset_pi_iff, mem_univ, forall_const] at h
    have : (univ.pi fun i ↦ (X.get i).toSet) ≠ ∅ := by
      apply Nonempty.ne_empty
      simp only [Set.univ_pi_nonempty_iff, DyadicInterval.toSet]
      intro i; rw [Set.nonempty_Icc]
      exact (X.get i).isValid'
    grind only [subset_iff, DyadicInterval.subset_iff]

@[simp, grind =]
theorem subset_iff_endpts : X ⊆ Y ↔ ∀ i : Fin n, (Y.get i).left ≤ (X.get i).left ∧
  (X.get i).right ≤ (Y.get i).right := by
  simp only [subset_iff]; apply forall_congr'
  intro i; rw [DyadicInterval.subset_iff_endpts]

@[simp, grind =]
theorem ssubset_iff : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y := by rfl

instance : Decidable (X ⊆ Y) := by simp only [subset_iff_endpts]; infer_instance
instance : Decidable (X ⊂ Y) := by simp only [ssubset_iff]; infer_instance

def intersection {k : ℕ} (U V : Vecterval k) : Option (Vecterval k) :=
  match k with
  | 0 => some #v[]
  | m + 1 =>
    let a := U.back ⊓ V.back
    let as : Option (Vecterval m) := intersection U.pop V.pop
    match a, as with
    | none, _ => none
    | _, none => none
    | some z, some zs => zs.push z
infixl:70 " ⊓ " => intersection

@[simp, grind =]
lemma inter_empty (X Y : Vecterval 0) : X ⊓ Y = some #v[] := by rfl

@[simp, grind =]
lemma inter_nonempty_eq_some {m : ℕ} (X Y Z : Vecterval (m + 1)) : X ⊓ Y = some Z ↔
  X.back ⊓ Y.back = some Z.back ∧ (X.pop) ⊓ (Y.pop) = Z.pop := by
  constructor
  · intro h; simp only [intersection] at h
    split at h
    · grind only
    · grind only
    · rename_i z zs h₁ h₂
      simp only [Option.some.injEq] at h
      simp only [h₁, h₂, ←h, Option.some.injEq]
      constructor
      · simp only [back_eq_getElem, add_tsub_cancel_right, getElem_push_eq]
      · simp only [pop_push]
  · intro h; simp only [intersection]
    split
    · grind only
    · grind only
    · rename_i z zs h₁ h₂
      simp only [h.1] at h₁; simp only [h.2] at h₂
      simp only [Option.some.injEq] at *
      rw [←push_pop_back Z]; congr <;> grind only

@[simp, grind =]
lemma inter_nonempty_eq_none  {m : ℕ} (X Y : Vecterval (m + 1)) : X ⊓ Y = none ↔
  X.back ⊓ Y.back = none ∨ intersection (X.pop) (Y.pop) = none := by
  constructor
  · intro h; simp only [intersection] at h
    split at h <;> grind only
  · intro h; simp only [intersection]
    split <;> grind only

@[simp, grind =]
theorem inter_eq_none_iff : X ⊓ Y = none ↔ ∃ i, X.get i ⊓ Y.get i = none := by
  induction n with
  | zero =>
    simp only [inter_empty, eq_empty]
    simp only [reduceCtorEq, get_mk, Fin.getElem_fin, List.getElem_toArray, IsEmpty.exists_iff]
  | succ m ih =>
    rw [inter_nonempty_eq_none, ih X.pop Y.pop]
    simp only [back_eq_getElem, add_tsub_cancel_right, get_pop]
    simp only [Fin.exists_fin_succ']
    rw [or_comm]; apply or_congr
    · grind only
    · norm_cast

@[simp, grind =]
theorem inter_eq_some_iff : X ⊓ Y = some Z ↔ ∀ i, X.get i ⊓ Y.get i = Z.get i := by
  induction n with
  | zero =>
    simp only [intersection, eq_empty]
    simp only [get_mk, Fin.getElem_fin, List.getElem_toArray, IsEmpty.forall_iff]
  | succ m ih =>
    rw [inter_nonempty_eq_some, ih X.pop Y.pop Z.pop]
    simp only [back_eq_getElem, add_tsub_cancel_right]
    simp only [Fin.forall_fin_succ']
    rw [and_comm]; apply and_congr_left; intro h
    apply forall_congr'; simp only [get_pop, implies_true]

@[simp, grind =]
theorem inter_self : X ⊓ X = some X := by
  grind only [inter_eq_some_iff, DyadicInterval.inter_self]

-- theorem inter_comm : X ⊓ Y = Y ⊓ X := by
--   grind only [intersection, inter_list_comm]

@[simp, grind →]
theorem inter_subset (h: Y ⊆ X) : X ⊓ Y = some Y := by
  grind only [subset_iff, inter_eq_some_iff, DyadicInterval.inter_subset]

@[simp, grind →]
theorem inter_subset_left (h: X ⊓ Y = some Z) : Z ⊆ X := by
  grind only [subset_iff, inter_eq_some_iff, DyadicInterval.inter_subset_left]

@[simp, grind →]
theorem inter_subset_right (h: X ⊓ Y = some Z) : Z ⊆ Y := by
  grind only [subset_iff, inter_eq_some_iff, DyadicInterval.inter_subset_right]

-- Maybe we don't need this at all!
-- theorem inter_optimal {V : Vecterval n} (hX : V ⊆ X) (hY : V ⊆ Y) : ∃ Z, X ⊓ Y = some Z ∧ V ⊆ Z := by
--   sorry

@[simp, grind →]
theorem inter_toSet_some (h: X ⊓ Y = some Z) : X.toSet ∩ Y.toSet = Z.toSet := by
  ext f; constructor
  · rw [mem_inter_iff]
    simp only [inter_eq_some_iff] at h
    simp only [toSet, mem_pi, mem_univ, forall_const]
    intro ⟨h₁, h₂⟩ i
    have h := DyadicInterval.inter_toSet_some _ _ _ (h i)
    grind only [mem_inter_iff]
  · rw [mem_inter_iff]
    simp only [inter_eq_some_iff] at h
    simp only [toSet, mem_pi, mem_univ, forall_const]
    intro hz; constructor
    · intro i
      have h := DyadicInterval.inter_toSet_some _ _ _ (h i)
      grind only [Set.mem_of_mem_inter_left]
    · intro i
      have h := DyadicInterval.inter_toSet_some _ _ _ (h i)
      grind only [Set.mem_of_mem_inter_right]

@[simp, grind →]
theorem inter_toSet_none (h: X ⊓ Y = none) : X.toSet ∩ Y.toSet = ∅ := by
  by_contra; simp only [← nonempty_iff_ne_empty, nonempty_def, mem_inter_iff] at this
  obtain ⟨f, hfx, hfy⟩ := this
  simp only [toSet, mem_pi, mem_univ, forall_const] at hfx hfy
  rw [inter_eq_none_iff] at h; obtain ⟨i, hi⟩ := h
  have hi := DyadicInterval.inter_toSet_none _ _ hi
  rw [← disjoint_iff_inter_eq_empty] at hi
  specialize hfx i; specialize hfy i
  have : ¬Disjoint (X.get i).toSet (Y.get i).toSet := by
    rw [not_disjoint_iff]; use f i
  grind only

def split_along (m : Fin n) : Vecterval n × Vecterval n :=
  let (left_half, right_half) := (X.get m).split
  let left_vec := X.set m left_half
  let right_vec := X.set m right_half
  ⟨left_vec, right_vec⟩

@[simp, grind .]
theorem left_split_subset (m : Fin n) : (X.split_along m).1 ⊆ X := by
  simp only [subset_iff, split_along]; intro i
  simp only [get_eq_getElem, getElem_set]
  grind only [DyadicInterval.left_split_subset, DyadicInterval.subset_refl]


@[simp, grind .]
theorem right_split_subset (m : Fin n) : (X.split_along m).2 ⊆ X := by
  simp only [subset_iff, split_along]; intro i
  simp only [get_eq_getElem, getElem_set]
  grind only [DyadicInterval.right_split_subset, DyadicInterval.subset_refl]

@[simp, grind .]
theorem mem_split (m : Fin n) : ∀ x ∈ X, x ∈ (X.split_along m).1 ∨
  x ∈ (X.split_along m).2 := by
  intro x hx; rw [mem_iff] at hx
  rcases DyadicInterval.mem_split _ _ (hx m) with h | h
  · left; simp only [mem_iff, split_along]
    simp only [get_eq_getElem, getElem_set] at *
    intro i; split_ifs with h'
    · simp only [← h', h]
    · simp only [hx]
  · right; simp only [mem_iff, split_along]
    simp only [get_eq_getElem, getElem_set] at *
    intro i; split_ifs with h'
    · simp only [← h', h]
    · simp only [hx]

end VectervalTopological
end Vecterval

abbrev Matrival (m n: ℕ) := Vector (Vecterval n) m

namespace Matrival
section IntervalMatrix
open Dyadic DyadicInterval Set Vector Matrix
variable {l m n : ℕ} (A B : Matrival m n)

def get (A : Matrival m n) (i : Fin m) (j : Fin n) : DyadicInterval := (Vector.get A i).get j

theorem get_eq_getElem (A : Matrival m n) (i : Fin m) (j : Fin n) : A.get i j = A[(i : ℕ)][(j : ℕ)] := rfl

def ofFn (f : Fin m → Fin n → DyadicInterval) : Matrival m n := Vector.ofFn (fun i ↦ Vecterval.ofFn (f i))

@[simp]
theorem get_ofFn (f : Fin m → Fin n → DyadicInterval) (i : Fin m) (j : Fin n) :
  (Matrival.ofFn f).get i j = f i j := by
  simp only [Matrival.ofFn, Matrival.get, Vector.get_ofFn, Vecterval.get_ofFn]

@[simp]
theorem getElem_ofFn (f : Fin m → Fin n → DyadicInterval) (i j : ℕ) (h : i < m)
  (h' : j < n) : (Matrival.ofFn f)[i][j] = f ⟨i, h⟩ ⟨j, h'⟩ := by
  simp only [Matrival.ofFn, Vector.getElem_ofFn, Vecterval.getElem_ofFn]

theorem ofFn_get_eq_self : Matrival.ofFn A.get = A := by
  apply Vector.ext; intro i hi
  apply Vector.ext; intro j hj
  simp only [getElem_ofFn, get_eq_getElem]

@[simp]
theorem eq_empty {M : Matrival 0 n} : M = #v[] := by simp only [Vector.eq_empty]

def one : Matrival n n := ofFn (1 : Matrix (Fin n) (Fin n) DyadicInterval)

def mem (A' : Matrix (Fin m) (Fin n) ℝ) : Prop := ∀ i, ∀ j, A' i j ∈ A.get i j
instance : Membership (Matrix (Fin m) (Fin n) ℝ) (Matrival m n) := ⟨mem⟩

theorem mem_iff (A' : Matrix (Fin m) (Fin n) ℝ) : A' ∈ A ↔ ∀ i, ∀ j, A' i j ∈ A.get i j := by rfl

theorem mem_iff_col (A' : Matrix (Fin m) (Fin n) ℝ) : A' ∈ A ↔ ∀ i, Vector.ofFn (A' i) ∈ Vector.get A i := by
  simp only [mem_iff, Vecterval.mem_iff, Vector.get_ofFn, Matrival.get]

theorem one_mem : (1 : Matrix (Fin n) (Fin n) ℝ) ∈ Matrival.one := by
  simp only [one, mem_iff, get_ofFn]; intro i j
  by_cases heq : i = j
  · rw [heq, one_apply_eq, one_apply_eq, ← Rat.cast_one, ← toRat_one]
    change ↑(toRat 1) ∈ ofDyadic 1
    grind only [to_rat_mem_of_dyadic]
  · rw [one_apply_ne heq, one_apply_ne heq, ← Rat.cast_zero, ← toRat_zero]
    change ↑(toRat 0) ∈ ofDyadic 0
    grind only [to_rat_mem_of_dyadic]

theorem sub_sound {A B : Matrival m n} {A' B': (Matrix (Fin m) (Fin n) ℝ)}
  (hA : A' ∈ A) (hB : B' ∈ B) : (A' - B') ∈ A - B := by
  simp only [mem_iff, get, Matrix.sub_apply, Vector.get_sub]; intro i j
  simp only [Pi.sub_apply, Vecterval.get_sub]
  change A' i j - B' i j ∈ A.get i j - B.get i j
  exact DyadicInterval.sub_sound _ _ _ (hA i j) _ (hB i j)

def mulVec (A : Matrival m n) (X : Vecterval n) : Vecterval m :=
  let A' : Matrix (Fin m) (Fin n) DyadicInterval:= A.get
  Vecterval.ofFn (A'.mulVecᵣ X.get )

theorem mulVec_sound {A : Matrival m n} {X : Vecterval n} {A' : (Matrix (Fin m) (Fin n) ℝ)}
  {x : Vector ℝ n} (hA : A' ∈ A) (hX : x ∈ X) : Vector.ofFn (A'.mulVecᵣ x.get) ∈ A.mulVec X := by
  simp only [Matrival.mulVec, Matrix.mulVecᵣ_eq, Vecterval.mem_iff, Vector.get_ofFn]
  intro i
  simp only [Matrix.mulVecᵣ, Matrix.dotProductᵣ_eq, FinVec.map_eq, Vecterval.get_ofFn,
    Function.comp_apply, Matrix.mulVec]
  unfold Matrival.get
  change (fun j ↦ A' i j) ⬝ᵥ x.get ∈ (Vector.get A i) ⬝ᵥ X
  apply Vecterval.dot_product_sound
  · simp only [Vecterval.mem_iff, Vector.get_ofFn]
    rw [mem_iff] at hA
    apply hA
  · simp only [Vecterval.mem_iff, Vector.get_ofFn]
    grind only [← Vecterval.mem_iff]

theorem mulVec_sound' {A : Matrival m n} {X : Vecterval n}
  {A' : Matrix (Fin m) (Fin n) ℝ} {x : Fin n → ℝ}
  (hA : A' ∈ A) (hX : Vector.ofFn x ∈ X) (i : Fin m) :
  A'.mulVec x i ∈ Matrix.mulVecᵣ A.get (Vector.get X) i := by
  have h₁ := Matrival.mulVec_sound hA hX i
  simp only [Matrix.mulVecᵣ_eq, Vector.get_ofFn, mulVec, Vecterval.get_ofFn] at h₁
  have h₂ : (Vector.ofFn x).get = x := by ext k; simp only [Vector.get_ofFn]
  grind only

instance : HMul (Matrival m n) (Vecterval n) (Vecterval m) := ⟨mulVec⟩

def vecMul (X : Vecterval m) (A : Matrival m n) : Vecterval n :=
  let A' : Matrix (Fin m) (Fin n) DyadicInterval:= A.get
  Vecterval.ofFn (A'.vecMulᵣ X.get)

instance : HMul (Vecterval m) (Matrival m n) (Vecterval n) := ⟨vecMul⟩

-- Note : Matrix mul is not sharp!
def mul (A : Matrival l m) (B : Matrival m n) : Matrival l n :=
  let A' : Matrix (Fin l) (Fin m) DyadicInterval:= A.get
  let B' : Matrix (Fin m) (Fin n) DyadicInterval:= B.get
  Matrival.ofFn (A' * B')

instance : HMul (Matrival l m) (Matrival m n) (Matrival l n) := ⟨mul⟩

theorem mul_sound {A : Matrival l m} {B : Matrival m n} {A' : (Matrix (Fin l) (Fin m) ℝ)}
  {B' : Matrix (Fin m) (Fin n) ℝ} (hA : A' ∈ A) (hB : B' ∈ B) : A' * B' ∈ A * B := by
  intro i j
  change  (A' * B') i j ∈ (Matrival.mul A B).get i j
  simp only [mul, get_ofFn, Matrix.mul_apply]
  apply Vecterval.sum_sound
  simp only [Finset.mem_univ, forall_const]
  intro k
  exact DyadicInterval.mul_sound _ _ _ (hA i k) _ (hB k j)

def rat_midpoint : Matrix (Fin m) (Fin n) ℚ := fun i j ↦ (A.get i j).midpoint.toRat

def ofRatWithPrec (prec : ℤ) (A : Matrix (Fin m) (Fin n) ℚ) : Matrival m n :=
  Matrival.ofFn (fun i j ↦ DyadicInterval.ofRatWithPrec prec (A i j))

theorem real_mem_matrival (prec : ℤ) (A : Matrix (Fin m) (Fin n) ℚ) :
  A.map Rat.cast ∈ ofRatWithPrec prec A := by
  grind only [ofRatWithPrec, mem_iff, get_ofFn, map_apply, rat_mem_of_rat]

/-- Appriximate Moore-Penrose Pseudoinverse for Rectangular matrices -/
def ApproxInverse (A : Matrival m n) : Matrix (Fin n) (Fin m) ℝ :=
  let B := (A.rat_midpoint).transpose * (A.rat_midpoint)
  let B' := ((1/B.det) • B.adjugate) * (A.rat_midpoint.transpose)
  fun i j ↦ B' i j

def ApproxInvWithPrec (prec : ℤ) (A : Matrival m n): Matrival n m :=
  let B := (A.rat_midpoint).transpose * (A.rat_midpoint)
  let B' := ((1/B.det) • B.adjugate) * (A.rat_midpoint.transpose)
  Matrival.ofFn (fun i j ↦ DyadicInterval.ofRatWithPrec prec (B' i j))

theorem approx_inverse_mem (prec : ℤ) (A : Matrival m n) : ApproxInverse A ∈ ApproxInvWithPrec prec A := by
  simp only [mem_iff]; intro i j
  simp only [ApproxInverse, ApproxInvWithPrec, get]
  simp only [Vector.get_eq_getElem, getElem_ofFn]
  generalize h : (((1 / (A.rat_midpoint.transpose * A.rat_midpoint).det) • (A.rat_midpoint.transpose * A.rat_midpoint).adjugate * A.rat_midpoint.transpose) i j) = q
  apply rat_mem_of_rat

def norm (A : Matrival m n) : Dyadic :=
  Finset.univ.fold max 0 (fun i ↦ Vecterval.norm (Vector.get A i))

theorem norm_nonneg (A : Matrival m n) : 0 ≤ A.norm := by
  simp only [norm]
  apply (Finset.le_fold_max 0).mpr
  left; rfl

def norm' (A : Matrival m n) :=
  -- Finset.univ.fold max 0 (fun i ↦ Vecterval.norm' (Vector.get A i))
  Finset.univ.sup (fun i ↦ Vecterval.norm' (Vector.get A i))

#check Matrix.linfty_opNNNorm_eq_opNNNorm
lemma mem_abs_le_row : ∀ A' ∈ A, ∀ i, ∑ j, ‖A' i j‖ ≤ (Vector.get A i).norm' := by
  intro A' hA' i; simp only [mem_iff] at hA'
  have hA₁ : ∀ i, ∀ j, |A' i j| ≤ ↑((A.get i j).abs.toRat)  := by
    grind only [mem_abs_le]
  simp only [Real.norm_eq_abs, Vecterval.norm', Vecterval.norm, NNReal.coe_mk]
  simp only [toRat_sum, Rat.cast_sum]; gcongr with j
  apply hA₁

theorem mem_abs_le : ∀ A' ∈ A, ∀ i, ∑ j, ‖A' i j‖ ≤ A.norm' := by
  intro A' hA' i
  apply le_trans (mem_abs_le_row A _ hA' i)
  simp only [norm']
  change (fun j ↦ (Vector.get A j).norm') i ≤ _
  apply Finset.le_sup (Finset.mem_univ i)

end IntervalMatrix
end Matrival


-- open DyadicInterval
-- def I₁ := ofRatWithPrec 5 ((7: ℚ)/9)
-- def I₂ := ofRatWithPrec 5 ((1: ℚ)/3)
-- def J₁ := ofRatWithPrec 6 ((2: ℚ)/5)
-- def J₂ := ofRatWithPrec 6 ((3: ℚ)/7)
-- -- def J₁ := ofRatWithPrec 5 ((7: ℚ)/9)
-- -- def J₂ := ofRatWithPrec 5 ((1: ℚ)/3)
-- def X : Vecterval 2 := ⟨#[I₁, I₂], by simp⟩
-- def Y : Vecterval 2 := ⟨#[J₁, J₂], by simp⟩
-- def Z : Vecterval 0 := #v[]

-- #eval X[0]
-- #eval Y
-- #eval X ⬝ᵥ Y
-- #eval (1 : Vecterval 2) ⬝ᵥ X
-- #eval (I₁ * J₁) + (I₂ * J₂)
-- #eval (X + Y)
-- #eval (X - Y)
-- #eval X.split_along 0

-- def A : Matrix (Fin 2) (Fin 2) DyadicInterval := 1
-- #eval (((A 0 0), (A 0 1)), ((A 1 0), (A 1 1)))
