import Mathlib

-- set_option diagnostics true

--A structure for *representatives of Dyadic Intervals*
structure DyadIntvRep where
  a : ℤ
  b : ℤ
  n : ℕ
--Removed isValid for completeness of the type
--It is better kept for semantic reasoning later on

namespace DyadIntvRep

def left (I : DyadIntvRep) : ℚ := mkRat I.a (2 ^ I.n)
def right (I : DyadIntvRep) : ℚ := mkRat I.b (2 ^ I.n)

def add (I J : DyadIntvRep) : DyadIntvRep :=
  let n' := max I.n J.n
  let a' := I.a * (2 ^ (n' - I.n)) + J.a * (2 ^ (n' - J.n))
  let b' := I.b * (2 ^ (n' - I.n)) + J.b * (2 ^ (n' - J.n))
  -- have h : a' ≤ b' := by
  --   unfold a' b'
  --   apply Int.add_le_add
  --   · rw[Int.mul_le_mul_iff_of_pos_right]
  --     · exact I.isValid
  --     · refine Int.pow_pos ?_
  --       exact Int.sign_eq_one_iff_pos.mp rfl
  --   · rw[Int.mul_le_mul_iff_of_pos_right]
  --     · exact J.isValid
  --     · refine Int.pow_pos ?_
  --       exact Int.sign_eq_one_iff_pos.mp rfl
  ⟨a', b', n'⟩

instance : Add DyadIntvRep where
  add := DyadIntvRep.add

def neg (I : DyadIntvRep) : DyadIntvRep :=
  ⟨-I.b, -I.a, I.n⟩

instance : Neg DyadIntvRep where
  neg := DyadIntvRep.neg

def sub (I J : DyadIntvRep) : DyadIntvRep :=
  I + (-J)

instance : Sub DyadIntvRep where
  sub := DyadIntvRep.sub

def mul (I J : DyadIntvRep) : DyadIntvRep :=
  let a' := min (min (I.a*J.a) (I.a*J.b)) (min (I.b*J.a) (I.b*J.b))
  let b' := max (max (I.a*J.a) (I.a*J.b)) (max (I.b*J.a) (I.b*J.b))
  -- have h : a' ≤ b' := by
  --   unfold a' b'
  --   refine Left.min_le_max_of_add_le_add ?_
  --   apply add_le_add
  --   · exact min_le_max
  --   · exact min_le_max
  ⟨a', b', (I.n+J.n)⟩

instance : Mul DyadIntvRep where
  mul := DyadIntvRep.mul

def equiv (I J : DyadIntvRep) : Prop :=
  (I.left = J.left) ∧ (I.right = J.right)

instance : Setoid DyadIntvRep where
  r := DyadIntvRep.equiv
  iseqv := by
    constructor
    · intro I
      unfold equiv
      simp only [and_self]
    · intro I J h
      unfold equiv at *
      constructor
      · exact h.left.symm
      · exact h.right.symm
    · intro I J K h₁ h₂
      unfold equiv at *
      constructor
      · exact Eq.trans h₁.left h₂.left
      · exact Eq.trans h₁.right h₂.right

--Not really needed for proofs; only for computation
instance : DecidableRel equiv := by --∀ I J, Decidable (I.equiv J)
  intro I J
  exact instDecidableAnd

instance : DecidableRel fun (I J : DyadIntvRep) ↦ (I ≈ J) := by
  intro I J
  simp [HasEquiv.Equiv]
  exact instDecidableAnd

@[simp]
lemma equiv_iff (I J : DyadIntvRep) : I ≈ J ↔ (I.left = J.left) ∧ (I.right = J.right) := by rfl

@[simp]
lemma add_right (I J : DyadIntvRep) : (I + J).right = I.right + J.right := by
  sorry

@[simp]
lemma add_left (I J : DyadIntvRep) : (I + J).left = I.left + J.left := by
  sorry

-- theorem add_comm : ∀ I J : DyadIntvRep, I + J ≈ J + I := by
--   intro I J
--   rw [equiv_iff]
--   constructor
--   · rw [add_left, add_left, Rat.add_comm]
--   · rw [add_right, add_right, Rat.add_comm]

lemma left_well_defined : ∀ (I J : DyadIntvRep), I ≈ J → I.left = J.left := by
  intro I J h
  simp only [equiv_iff] at h
  exact h.left

lemma right_well_defined :  ∀ (I J : DyadIntvRep), I ≈ J → I.right = J.right := by
  intro I J h
  simp only [equiv_iff] at h
  exact h.right

end DyadIntvRep

def I : DyadIntvRep := ⟨(-3), 1, 4⟩
def I' : DyadIntvRep := ⟨(-6), 2, 5⟩
def J : DyadIntvRep := ⟨(-7), (-2), 2⟩
#eval I.left
#eval I.right
#eval I ≈ I'
#eval I.equiv J

#check Quotient
#check DyadIntvRep.instSetoid
#check Quotient.mk' I
#check DyadIntvRep.instSetoid

def DyadicInterval := Quotient DyadIntvRep.instSetoid

#check DyadicInterval

#check Quotient.lift DyadIntvRep.left DyadIntvRep.left_well_defined

namespace DyadicInterval
--Now lift functions
def left (I : DyadicInterval) : ℚ :=
  Quotient.lift DyadIntvRep.left DyadIntvRep.left_well_defined I
def right (I : DyadicInterval) : ℚ :=
  Quotient.lift DyadIntvRep.right DyadIntvRep.right_well_defined I

end DyadicInterval

def I₁ : DyadicInterval := Quotient.mk' I
def I₁' : DyadicInterval := Quotient.mk' I'
#eval I₁.left
#eval I₁.right
-- #eval I₁ = I₁' failed to synthesize Decidable (I₁ = I₁')
