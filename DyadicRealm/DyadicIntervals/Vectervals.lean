import Mathlib
-- import LeanCert
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false

abbrev Vecterval (n : ℕ) := Vector DyadicInterval n

#check Vector.add

namespace Vecterval

section VectervalStructural
open Dyadic DyadicInterval Set
variable {n : ℕ} (X Y : Vecterval n)

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

theorem mem_iff (x : Vector ℝ n) : x ∈ X ↔ ∀ i : Fin n, x.get i ∈ X.get i := by rfl

theorem mem_iff_get_mem_toSet (x : Vector ℝ n) : x ∈ X ↔ x.get ∈ X.toSet := by
  simp only [mem_iff, toSet, mem_pi, mem_univ, forall_const]; rfl

theorem mem_iff_le_endpts (x : Vector ℝ n) :  x ∈ X ↔ ∀ i : Fin n,
  (X.get i).left.toRat ≤ x.get i ∧ x.get i ≤ (X.get i).right.toRat := by
  simp only [mem_iff, DyadicInterval.mem_iff_le_endpts]

end VectervalStructural

section VectervalTopological
open Dyadic DyadicInterval Set
variable {n : ℕ} (X Y Z: Vecterval n)

def subset := ∀ i : Fin n, X.get i ⊆ Y.get i
instance : HasSubset (Vecterval n) := ⟨Vecterval.subset⟩
instance : HasSSubset (Vecterval n) where SSubset X Y := X ⊆ Y ∧ X ≠ Y

theorem subset_iff : X ⊆ Y ↔ ∀ i : Fin n, X.get i ⊆ Y.get i := by rfl

theorem subset_iff_toSet : X ⊆ Y ↔ X.toSet ⊆ Y.toSet := by
  sorry

theorem subset_iff_endpts : X ⊆ Y ↔ ∀ i : Fin n, (Y.get i).left ≤ (X.get i).left ∧
  (X.get i).right ≤ (Y.get i).right := by
  sorry

def intersection : Option (Vecterval n) :=
  let K := Vector.zipWith DyadicInterval.intersection X Y
  K.mapM id
infixl:70 " ⊓ " => intersection

theorem inter_self : X ⊓ X = some X := by
  sorry

theorem inter_comm : X ⊓ Y = Y ⊓ X := by
  sorry

theorem inter_subset (h: Y ⊆ X) : X ⊓ Y = some Y := by
  sorry

theorem inter_subset_left (h: X ⊓ Y = some Z) : Z ⊆ X := by
  sorry

theorem inter_subset_right (h: X ⊓ Y = some Z) : Z ⊆ Y := by
  sorry

theorem inter_optimal {V : Vecterval n} (hX : V ⊆ X) (hY : V ⊆ Y) : ∃ Z, X ⊓ Y = some Z ∧ V ⊆ Z := by
  sorry

theorem inter_toSet_some (h: X ⊓ Y = some Z) : X.toSet ∩ Y.toSet = Z.toSet := by
  sorry

theorem inter_toSet_none (h: X ⊓ Y = some Z) : X.toSet ∩ Y.toSet = ∅ := by
  sorry

def split_along (m : Fin n) : Vecterval n × Vecterval n :=
  let (left_half, right_half) := (X.get m).split
  let left_vec := X.set m left_half
  let right_vec := X.set m right_half
  ⟨left_vec, right_vec⟩

theorem left_split_subset (m : Fin n) : (X.split_along m).1 ⊆ X := by
  sorry

theorem right_split_subset (m : Fin n) : (X.split_along m).2 ⊆ X := by
  sorry

theorem mem_split_iff (m : Fin n) : ∀ x ∈ X, x ∈ (X.split_along m).1 ∨
  x ∈ (X.split_along m).2 := by
    sorry

#check Vecterval
#check Matrix.mulVec

end VectervalTopological
end Vecterval


open DyadicInterval
def I₁ := ofRatWithPrec 5 ((7: ℚ)/9)
def I₂ := ofRatWithPrec 5 ((1: ℚ)/3)
def J₁ := ofRatWithPrec 4 ((2: ℚ)/5)
def J₂ := ofRatWithPrec 4 ((3: ℚ)/7)
-- def J₁ := ofRatWithPrec 5 ((7: ℚ)/9)
-- def J₂ := ofRatWithPrec 5 ((1: ℚ)/3)
def X : Vecterval 2 := ⟨#[I₁, I₂], by simp⟩
def Y : Vecterval 2 := ⟨#[J₁, J₂], by simp⟩
#eval X
#eval Y
#eval (X + Y)
#eval (X - Y)
#eval X.split_along 0
#eval (4 : DyadicInterval) • X
