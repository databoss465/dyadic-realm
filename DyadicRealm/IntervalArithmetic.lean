import Mathlib
open Dyadic Finset
-- set_option diagnostics true

structure DyadIntvRep where
  a : ℤ
  b : ℤ
  n : ℕ
deriving DecidableEq

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
  simp only[HasEquiv.Equiv]
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

---------------------------------------------------------------------

#check  Dyadic.toRat
#check Rat.toDyadic
#check Finset.max'

namespace Dyadic

-- def maxDy (a b : Dyadic) : Dyadic := if a ≤ b then b else a

-- def minDy (a b : Dyadic) : Dyadic := if a ≤ b then a else b

-- instance : Max Dyadic := ⟨Dyadic.maxDy⟩

-- instance : Min Dyadic := ⟨Dyadic.minDy⟩

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

theorem add_le_add' {a b c d : Dyadic} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  simp only [le_iff_toRat, toRat_add] at *
  exact add_le_add h₁ h₂

end Dyadic

structure DyadicInterval where
  left : Dyadic
  right : Dyadic
  isValid : left ≤ right
  deriving DecidableEq

---------------------------------------------------------------------
namespace DyadicInterval
section
variable (I J K : DyadicInterval)

def add : DyadicInterval :=
  let l := I.left + J.left
  let r := I.right + J.right
  have h : l ≤ r := add_le_add' I.isValid J.isValid
  ⟨l, r, h⟩

instance : Add DyadicInterval := ⟨DyadicInterval.add⟩

def neg (I : DyadicInterval) : DyadicInterval :=
  have h : -I.right ≤ -I.left := by
     simp only [le_iff_toRat, toRat_neg, neg_le_neg_iff]
     rw [← le_iff_toRat]
     exact I.isValid
  ⟨-I.right, -I.left, h⟩

instance : Neg DyadicInterval := ⟨DyadicInterval.neg⟩

def sub : DyadicInterval := I + (-J)

instance : Sub DyadicInterval where
  sub := DyadicInterval.sub

def productEndpts : Finset Dyadic :=
  {(I.left * J.left),
  (I.left * J.right),
  (I.right * J.left),
  (I.right * J.right)}

@[simp]
lemma product_endpts_nonempty : (productEndpts I J).Nonempty := by
  unfold productEndpts
  exact insert_nonempty (I.left * J.left) {I.left * J.right, I.right * J.left, I.right * J.right}

def mul : DyadicInterval :=
  let s := productEndpts I J
  have hs := product_endpts_nonempty I J
  ⟨min' s hs, max' s hs, min'_le_max' s hs⟩

instance : Mul DyadicInterval := ⟨DyadicInterval.mul⟩

@[simp]
theorem left_add_eq : (I + J).left = I.left + J.left := by rfl

@[simp]
theorem right_add_eq : (I + J).right = I.right + J.right := by rfl

@[simp]
lemma mul_left_endpt : (I * J).left =
  (productEndpts I J).min' (product_endpts_nonempty I J) := by rfl

@[simp]
lemma mul_right_endpt : (I * J).right =
  (productEndpts I J).max' (product_endpts_nonempty I J) := by rfl
@[simp]
lemma neg_left : (- I).left = -I.right := by rfl

@[simp]
lemma neg_right : (-I).right = -I.left := by rfl

@[simp]
theorem eq_iff_left_right : I = J ↔ I.left = J.left ∧ I.right = J.right := by
  constructor
  · intro h
    cases I
    cases J
    simp only [mk.injEq] at *
    exact h
  · intro h
    cases I
    cases J
    simp only [mk.injEq] at *
    exact h

--review this
@[simp]
lemma product_endpts_comm : productEndpts I J = productEndpts J I := by
  simp only [productEndpts, Dyadic.mul_comm]
  grind only [= Set.mem_singleton_iff, = mem_singleton, = insert_eq_of_mem, = mem_insert, cases Or]

-- FALSE!
-- lemma product_endpts_assoc : productEndpts (I * J) K = productEndpts I (J * K) := by
--   sorry

theorem add_comm : I + J = J + I := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_comm, and_self]

theorem add_assoc : (I + J) + K = I + (J + K) := by
  simp only [eq_iff_left_right, left_add_eq, right_add_eq, Dyadic.add_assoc, and_self]

theorem mul_comm : I * J = J * I := by
  simp only [eq_iff_left_right, mul_left_endpt, mul_right_endpt, product_endpts_comm, and_self]

-- NOT TRUE
-- theorem mul_assoc : (I * J) * K = I * (J * K) := by
--   rw [eq_iff_left_right]
--   constructor
--   · simp only [mul_left_endpt]
--     sorry
--   · sorry

-- theorem add_mul : (I + J) * K = I * K + I * J := by
--   sorry

-- theorem mul_add : I * (J + K) = I * J + I * K := by
--   sorry

theorem neg_mul : -I * J = - (I * J) := by
  simp only [eq_iff_left_right]
  constructor
  · sorry
  · sorry

-- neg_add_cancel is not true!
end
end DyadicInterval

def a := Dyadic.ofOdd (-3) 5 (by ring)
def b := Dyadic.ofOdd (7) 3 (by ring)
def I : DyadicInterval := ⟨a, b, by decide⟩
def J : DyadicInterval := ⟨a, b, by decide⟩
def J' : DyadicInterval := ⟨(a-1), b, by decide⟩
#eval I = J
#eval I = J'
#eval (I + J).left.toRat
#eval (I + J).right.toRat
#eval (I * J).left.toRat
#eval (I * J).right.toRat
