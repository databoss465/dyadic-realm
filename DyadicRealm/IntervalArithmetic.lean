import Mathlib

set_option diagnostics true

structure DyadicInterval where
  a : ℤ
  b : ℤ
  n : ℕ
  isValid : a ≤ b

#check DyadicInterval.mk

namespace DyadicInterval

def left (I : DyadicInterval) : ℚ := I.a / (2 ^ I.n)
def right (I : DyadicInterval) : ℚ := I.b / (2 ^ I.n)

def add (I J : DyadicInterval) : DyadicInterval :=
  let n' := max I.n J.n
  let a' := I.a * (2 ^ (n' - I.n)) + J.a * (2 ^ (n' - J.n))
  let b' := I.b * (2 ^ (n' - I.n)) + J.b * (2 ^ (n' - J.n))
  have h : a' ≤ b' := by
    unfold a' b'
    apply Int.add_le_add
    · rw[Int.mul_le_mul_iff_of_pos_right]
      · exact I.isValid
      · refine Int.pow_pos ?_
        exact Int.sign_eq_one_iff_pos.mp rfl
    · rw[Int.mul_le_mul_iff_of_pos_right]
      · exact J.isValid
      · refine Int.pow_pos ?_
        exact Int.sign_eq_one_iff_pos.mp rfl
  ⟨a', b', n', h⟩

instance : Add DyadicInterval where
  add := DyadicInterval.add

def neg (I : DyadicInterval) : DyadicInterval :=
  ⟨-I.b, -I.a, I.n, Int.neg_le_neg I.isValid⟩

instance : Neg DyadicInterval where
  neg := DyadicInterval.neg

def sub (I J : DyadicInterval) : DyadicInterval :=
  I + (-J)

instance : Sub DyadicInterval where
  sub := DyadicInterval.sub

def mul (I J : DyadicInterval) : DyadicInterval :=
  let a' := min (min (I.a*J.a) (I.a*J.b)) (min (I.b*J.a) (I.b*J.b))
  let b' := max (max (I.a*J.a) (I.a*J.b)) (max (I.b*J.a) (I.b*J.b))
  have h : a' ≤ b' := by
    unfold a' b'
    refine Left.min_le_max_of_add_le_add ?_
    apply add_le_add
    · exact min_le_max
    · exact min_le_max
  ⟨a', b', (I.n+J.n), h⟩

instance : Mul DyadicInterval where
  mul := DyadicInterval.mul

def equiv (I J : DyadicInterval) : Prop :=
  (I.left = J.left) ∧ (I.right = J.right)

instance : DecidableRel equiv := by --∀ I J, Decidable (I.equiv J)
  intro I J
  exact instDecidableAnd

instance : HasEquiv DyadicInterval where  --Syntactic sugar
  Equiv := DyadicInterval.equiv

instance : DecidableRel fun (I J : DyadicInterval) ↦ (I ≈ J) := by
  intro I J
  simp [HasEquiv.Equiv]
  exact instDecidableAnd

-- Needs more work on ≈
-- To make it cleaner maybe we also need fun a m ↦ [a/2^m, a/2^m]
theorem singleton_eq {I: DyadicInterval}(h : I.a = I.b) :
  ∀ m : ℕ, I ≈ ⟨I.a, I.b, m, le_of_eq h⟩ := by
  intro m
  sorry

lemma add_comm : ∀ I J : DyadicInterval, I + J = J + I := by
  sorry

end DyadicInterval

def I : DyadicInterval := ⟨(-3), 1, 4, by decide⟩
def I' : DyadicInterval := ⟨(-6), 2, 5, by decide⟩
def J : DyadicInterval := ⟨(-7), (-2), 2, by decide⟩

#eval I.left
#eval I.right
#eval I ≈ I'
#eval I.equiv J
