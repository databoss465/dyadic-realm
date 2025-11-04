import Mathlib

-- set_option diagnostics true

--A structure for *representatives of Dyadic Intervals*
structure DyadIntvRep where
  a : ℤ
  b : ℤ
  n : ℕ
deriving DecidableEq
--Removed isValid for completeness of the type
--It is better kept for semantic reasoning later on

#check  Dyadic.toRat
#check Rat.toDyadic

namespace DyadIntvRep

def left (I : DyadIntvRep) : Dyadic := Dyadic.ofIntWithPrec I.a I.n
def right (I : DyadIntvRep) : Dyadic := Dyadic.ofIntWithPrec I.b I.n

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
      simp only [equiv, and_self]
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

--NOT TRUE
-- We are only guaranteed a₁.add b₁ ≈ a₂.add b₂
-- lemma add_well_defined : ∀ (a₁ b₁ a₂ b₂ : DyadIntvRep),
--   a₁ ≈ a₂ → b₁ ≈ b₂ → a₁.add b₁ = a₂.add b₂ := by
--   sorry
end DyadIntvRep

def I : DyadIntvRep := ⟨(-3), 1, 4⟩
def I' : DyadIntvRep := ⟨(-6), 2, 5⟩
def J : DyadIntvRep := ⟨(-7), (-2), 2⟩
#eval I.left
#eval I.right
#eval I ≈ I'
#eval I.equiv J

#check add_le_add

-- ------------------------------------------------------------------
structure DyadicInterval where
  left : Dyadic
  right : Dyadic
  isValid : left ≤ right

namespace Dyadic

instance : Preorder Dyadic where
  le x y := toRat x ≤ toRat y
  lt x y := toRat x < toRat y
  le_refl x := by rfl
  le_trans x y z h₁ h₂ := le_trans h₁ h₂
  lt_iff_le_not_ge x y := Rat.lt_iff_le_not_ge x.toRat y.toRat

theorem add_le_add' {a b c d : Dyadic} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  simp only [le_iff_toRat, toRat_add] at *
  exact add_le_add h₁ h₂

end Dyadic
namespace DyadicInterval

def add (I J : DyadicInterval) : DyadicInterval :=
  let l := I.left + J.left
  let r := I.right + J.right
  have h : l ≤ r := Dyadic.add_le_add' I.isValid J.isValid
  ⟨l, r, h⟩

instance : Add DyadicInterval where
  add := DyadicInterval.add

def neg (I : DyadicInterval) : DyadicInterval :=
  have h : -I.right ≤ -I.left := by sorry
  ⟨-I.right, -I.left, h⟩

end DyadicInterval

#check Dyadic.ofOdd (-3) 5 (by ring)
#eval Dyadic.ofIntWithPrec (-3) 4
