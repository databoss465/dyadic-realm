import Mathlib
-- import LeanCert
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Vector

theorem get_pop {α : Type} {n : ℕ} (v : Vector α (n + 1))(i : Fin n) :
  (v.pop).get i = v.get i.castSucc := by
  simp only [get, Nat.add_one_sub_one, pop, Fin.val_cast, Array.getElem_pop, getElem_toArray,
    Fin.val_castSucc]

end Vector

abbrev Vecterval (n : ℕ) := Vector DyadicInterval n

namespace Vecterval

section VectervalStructural
open Dyadic DyadicInterval Set Vector
variable {n : ℕ} (X Y : Vecterval n)

def zero : Vecterval n := replicate _ 0
instance : Zero (Vecterval n) := ⟨zero⟩

def one : Vecterval n := replicate _ 1
instance : One (Vecterval n) := ⟨one⟩

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

def midpoint : Vector Dyadic n := X.map (fun I ↦ I.midpoint)

/-- Set of functions `f : Fin n → ℝ` such that for every coordinate `i`,
    `f i` lies in the interval `X.get i`. -/
def toSet := Set.pi Set.univ (fun i => (X.get i).toSet)

@[simp, grind .]
theorem nonempty : X.toSet.Nonempty := by
  simp [toSet, Set.univ_pi_nonempty_iff, DyadicInterval.nonempty]

@[simp, grind =]
theorem mem_iff (x : Vector ℝ n) : x ∈ X ↔ ∀ i : Fin n, x.get i ∈ X.get i := by rfl

@[simp, grind =]
theorem mem_iff_get_mem_toSet (x : Vector ℝ n) : x ∈ X ↔ x.get ∈ X.toSet := by
  simp only [mem_iff, toSet, mem_pi, mem_univ, forall_const]; rfl

@[simp, grind =]
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

def abs {n : ℕ} (X : Vecterval n) : Dyadic :=
  (X.map (fun I ↦ I.abs)).sum

def dotProduct : DyadicInterval := X.get ⬝ᵥ Y.get
infixl:72 " ⬝ᵥ " => dotProduct

@[simp, grind =]
theorem dotProduct_comm : X ⬝ᵥ Y = Y ⬝ᵥ X := by simp only [dotProduct, _root_.dotProduct_comm]

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
open Dyadic DyadicInterval Set Vector
variable {l m n : ℕ} (A : Matrival m n)

def get (A : Matrival m n) (i : Fin m) (j : Fin n) : DyadicInterval := (Vector.get A i).get j
#check A.get
#check (A.get : Matrix (Fin m) (Fin n) DyadicInterval)

theorem get_eq_getElem (A : Matrival m n) (i : Fin m) (j : Fin n) : A.get i j = A[(i : ℕ)][(j : ℕ)] := rfl

def ofFn (f : Fin m → Fin n → DyadicInterval) : Matrival m n := Vector.ofFn (fun i ↦ Vecterval.ofFn (f i))

theorem get_ofFn (f : Fin m → Fin n → DyadicInterval) (i : Fin m) (j : Fin n) :
  (Matrival.ofFn f).get i j = f i j := by
  simp only [Matrival.ofFn, Matrival.get, Vector.get_ofFn, Vecterval.get_ofFn]

theorem getElem_ofFn (f : Fin m → Fin n → DyadicInterval) (i j : ℕ) (h : i < m)
  (h' : j < n) : (Matrival.ofFn f)[i][j] = f ⟨i, h⟩ ⟨j, h'⟩ := by
  simp only [Matrival.ofFn, Vector.getElem_ofFn, Vecterval.getElem_ofFn]

theorem ofFn_get_eq_self : Matrival.ofFn A.get = A := by
  apply Vector.ext; intro i hi
  apply Vector.ext; intro j hj
  simp only [getElem_ofFn, get_eq_getElem]

def mul (A : Matrival l m) (B : Matrival m n) : Matrival l n :=
  let A' : Matrix (Fin l) (Fin m) DyadicInterval:= A.get
  let B' : Matrix (Fin m) (Fin n) DyadicInterval:= B.get
  Matrival.ofFn (A' * B')

instance : HMul (Matrival l m) (Matrival m n) (Matrival l n) := ⟨mul⟩

def mulVec (A : Matrival m n) (X : Vecterval n) : Vecterval m :=
  let A' : Matrix (Fin m) (Fin n) DyadicInterval:= A.get
  Vecterval.ofFn (A'.mulVecᵣ X.get )

instance : HMul (Matrival m n) (Vecterval n) (Vecterval m) := ⟨mulVec⟩

def vecMul (X : Vecterval m) (A : Matrival m n) : Vecterval n :=
  let A' : Matrix (Fin m) (Fin n) DyadicInterval:= A.get
  Vecterval.ofFn (A'.vecMulᵣ X.get)

instance : HMul (Vecterval m) (Matrival m n) (Vecterval n) := ⟨vecMul⟩

def rat_midpoint : Matrix (Fin m) (Fin n) ℚ := fun i j ↦ ↑(A.get i j).midpoint.toRat

/-- Appriximate Moore-Penrose Pseudoinverse for Rectangular matrices -/
def ApproxInvWithPrec (prec : ℤ) (A : Matrival m n): Matrival n m :=
  let B := (A.rat_midpoint).transpose * (A.rat_midpoint)
  let B' := ((1/B.det) • B.adjugate) * (A.rat_midpoint.transpose)
  Matrival.ofFn (fun i j ↦ ofRatWithPrec prec (B' i j))

def norm (A : Matrival m n) : Dyadic :=
  let M := A.map (fun X ↦ X.abs)
  match M.toList with
  | [] => 0
  | x :: xs => (x :: xs).max (by grind only)

end IntervalMatrix
end Matrival


open DyadicInterval
def I₁ := ofRatWithPrec 5 ((7: ℚ)/9)
def I₂ := ofRatWithPrec 5 ((1: ℚ)/3)
def J₁ := ofRatWithPrec 6 ((2: ℚ)/5)
def J₂ := ofRatWithPrec 6 ((3: ℚ)/7)
-- def J₁ := ofRatWithPrec 5 ((7: ℚ)/9)
-- def J₂ := ofRatWithPrec 5 ((1: ℚ)/3)
def X : Vecterval 2 := ⟨#[I₁, I₂], by simp⟩
def Y : Vecterval 2 := ⟨#[J₁, J₂], by simp⟩
def Z : Vecterval 0 := #v[]
#eval X[0]
#eval Y
#eval X ⬝ᵥ Y
#eval (1 : Vecterval 2) ⬝ᵥ X
#eval (I₁ * J₁) + (I₂ * J₂)
#eval (X + Y)
#eval (X - Y)
#eval X.split_along 0
