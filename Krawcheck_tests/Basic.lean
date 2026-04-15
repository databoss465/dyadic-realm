import Krawcheck
set_option linter.style.longLine false

section NewtonTesting
open Rat DyadicInterval RatPol

-- Remember this case. Keep it don't change
def I : DyadicInterval := ⟨0, 2, (by sorry)⟩
def p : RatPol 3 := #v[1, -2, 1] -- x^2 - 2x + 1
#eval! deriv p
#eval! intervalEvalWithPrec 10 (deriv p) I -- [[-2, 2]]
#eval! IsolateRoots I p 10 10 0
-- Newton Operator cannot fundamentally detect multiple roots.

-- Case 1
def I₁ : DyadicInterval := ⟨(toDyadic (-1/2) 2), 2 , (by sorry)⟩ --[[-1/2, 2]]
def p₁ : RatPol 3 := #v[-1, 0, 1] -- x^2 - 1
#eval! IsolateRoots I₁ p₁ 6 5 0 --([[[3/4, 2]]], [])

-- Case 2
def I₂ : DyadicInterval := ⟨(toDyadic (-1/2) 2), 1 , (by sorry)⟩ -- [[-1/2, 1]]
def p₂ : RatPol 4 := #v[0, 0, 0, 1] -- x^3
#eval! IsolateRoots I₂ p₂ 5 5 0 -- ([], [[[-1/32, 1/64]]])

-- Case 3
def I₃ : DyadicInterval :=
  ⟨(toDyadic ((5/4 : ℚ)) 2), (toDyadic ((3/2)) 2), (by sorry)⟩ -- [5/4, 3/2]
def p₃ : RatPol 3 := #v[-2, 0, 1] -- x^2 - 2
#eval! Newton 5 I₃ p₃ ⊆ I₃
#eval! IsolateRoots I₃ p₃ 5 5 0 -- ([[[5/4, 3/2]]], [])

-- Case 4
def I₄ : DyadicInterval := ⟨3,4, (by grind)⟩ --[3, 4]
def p₄ : RatPol 5 := #v[2, 0, 3, 0, 1] -- x^4 + 3x^2 + 2
#eval! Newton 5 I₄ p₄ ⊓ I₄
#eval! IsolateRoots I₄ p₄ 5 5 0 -- ([], [])

-- Case 5
def I₅ : DyadicInterval := ⟨-3,0, (by grind)⟩ --[-3, 0]
def p₅ : RatPol 4 := #v[-6, -7, 0, 1] -- x^3 - 7x - 6
#eval! IsolateRoots I₅ p₅ 5 5 0 -- ([[[-9/4, -15/8]], [[-69/64, -29/32]]], [])

end NewtonTesting

section KrawczykTesting
open Rat Vecterval Matrival System

def Y (S : System 2 2) (X : Vecterval 2) := (ApproxInvWithPrec 10 (jacobianEvalWithPrec 10 S X)).rat_midpoint

-- Circle and Parabola
def V : Vecterval 2 := #v[⟨-5,5, by decide⟩, ⟨-5, 5, by decide⟩]                   --[[-5, 5]] × [[-5, 5]]

def q₁ : MvRatPol 2 := [(1, #v[2, 0]), (1, #v[0, 2]), (-5, #v[0, 0])]     -- x1^2 + x2^2 - 5
def q₂ :  MvRatPol 2 := [(1, #v[2, 0]), (-1, #v[0, 1]), (-3, #v[0, 0])]   -- x1^2 - x2 - 3
def S₀ : System 2 2 := #v[q₁, q₂]

#eval! vectervalEvalWithPrec 5 S₀ V
#eval! isValidKrawczyk 10 S₀ (Y S₀ V) V

-- At prec 5 and max_depth 10, finds all 4 roots
-- For smaller intervals, we need less depth to find the roots
#eval! (IsolateRoots 10 S₀ (Y S₀) V 10)

-- Another 2x2 System
-- 2 Roots: [[0, 0.5]] × [[0, 0.5]], [[0, 0.5]] × [[0.5, 1]]
-- Also has a root in [[1, 2]] × [[-2, -3]]

def V₀ : Vecterval 2 := #v[dy[[0,1/2]], dy[[0,1]]]
def V₁ : Vecterval 2 := #v[dy[[-1,0]], dy[[0,1]]]
def V₂ : Vecterval 2 := #v[dy[[3/2, 2]], dy[[-5/2, 2]]]
def S : System 2 2 := poly[x1^3, x2^3, -3/2 * x1 * x2;
  4 * x1^2 * x2, 9/4 * x1 * x2^2, -1/2 * x1, -5/2 * x2, 1]

/-- info: ([#v[dy[[1/16, 1/8]], dy[[3/8, 7/16]]], #v[dy[[3/8, 7/16]], dy[[11/16, 3/4]]]], []) -/
#guard_msgs in
#eval Vecterval.IsolateRoots 10 S (Y_default S) V₀ 9
-- #eval #v[dy[[1/16, 1/8]], dy[[3/8, 7/16]]]
-- #eval #v[dy[[3/8, 7/16]], dy[[11/16, 3/4]]]

example : (Vecterval.IsolateRoots 10 S (Y_default S) V₀ 9).1 =
  [#v[dy[[1/16, 1/8]], dy[[3/8, 7/16]]], #v[dy[[3/8, 7/16]], dy[[11/16, 3/4]]] ] := by native_decide

example : V₀.HasRoot S := by
  apply krawcheck_has_root 10 9
  native_decide
  -- decide +kernel

example : V₀.HasRoot S := by krawcheck

/-- info: ([#v[dy[[25/16, 13/8]], dy[[-133/64, -257/128]]]], []) -/
#guard_msgs in
#eval (Vecterval.IsolateRoots 10 S (Y_default S) V₂ 9)
-- #eval #v[dy[[25/16, 13/8]], dy[[-133/64, -257/128]] ]

example : (Vecterval.IsolateRoots 10 S (Y_default S) V₂ 9).1 =
  [#v[dy[[25/16, 13/8]], dy[[-133/64, -257/128]] ] ] := by native_decide

example : (Vecterval.IsolateRoots 10 S (Y_default S) V₂ 9).2 = [] := by native_decide

example : V₂.HasUniqueRoot S := by
  apply krawcheck_has_unique_root 10 10
  <;> native_decide
  -- <;> decide +kernel

example : V₂.HasUniqueRoot S := by krawcheck

/-- info: ([], []) -/
#guard_msgs in
#eval Vecterval.IsolateRoots 1 S (Y_default S) V₁ 6

example : Vecterval.IsolateRoots 1 S (Y_default S) V₁ 6 = ([], []) := by native_decide

example : V₁.HasNoRoot S := by
  apply krawcheck_has_no_root 1 6
  native_decide
  -- decide +kernel

example : V₁.HasNoRoot S := by krawcheck

-- Degenerate System
def U : Vecterval 2 := #v[⟨0,1, by grind⟩, ⟨0,1,by grind⟩]
def t : MvRatPol 2 := [(2, #v[2,0]), (4, #v[1,1]), (-1, #v[0,2]), (-1, #v[0,0])]
def T : System 2 2 := #v[t, t]

#eval! IsolateRoots 10 T (Y T) U 6

-- Tangent System
def W₀ : Vecterval 2 := #v[⟨-1,0, by grind⟩, ⟨0,1,by grind⟩] -- Multiple root
def W₁ : Vecterval 2 := #v[⟨0,1, by grind⟩,
  ⟨(toDyadic (-3/2) 2),(toDyadic (3/2) 2),by grind⟩] -- 2 Roots
-- def r₁ : MvRatPol 2 := [(1, #v[2, 0]), (-2/3, #v[1, 0]), (1, #v[0, 2]), (-8/9, #v[0,0])]
-- def r₂ : MvRatPol 2 := [(-1, #v[1, 0]), (1, #v[0, 2]), (-2/3, #v[0,0])]
-- def R : System 2 2 := #v[r₁, r₂]
def R : System 2 2 := poly[x1 ^ 2, -2 / 3 * x1, x2 ^ 2, -8/9 ; -1 * x1, x2 ^ 2, -2/3]

#eval! IsolateRoots 10 R (Y R) W₁ 10
#eval! IsolateRoots 10 R (Y R) W₀ 13


-- 3x3 system
def Y' (S : System 3 3) (X : Vecterval 3) := (ApproxInvWithPrec 10 (jacobianEvalWithPrec 10 S X)).rat_midpoint

def X : Vecterval 3 := Vector.replicate 3 ⟨(toDyadic (-3/2) 2),(toDyadic (3/2) 2),by grind⟩
def X' : Vecterval 3 := Vector.replicate 3 ⟨(toDyadic (-3/2) 2),0,by sorry⟩

-- def a₁ : MvRatPol 3 := [(1, #v[2, 0, 0]), (1, #v[0, 2, 0]), (1, #v[0, 0, 2]), (-3, #v[0, 0, 0])]
-- def a₂ : MvRatPol 3 := [(1, #v[2, 0, 0]), (-1, #v[0, 1, 0]), (-1, #v[0, 0, 1]), (1, #v[0, 0, 0])]
-- def a₃ : MvRatPol 3 := [(1, #v[1, 0, 0]), (-1, #v[0, 1, 0]), (1, #v[0, 0, 1]), (-1, #v[0, 0, 0])]
-- def A : System 3 3 := #v[a₁, a₂, a₃]
def A : System 3 3 := poly[x1^2, x2^2, x3^2, -3; x1^2, -1*x2, -1*x3, 1; x1, -1*x2, x3, -1]

#eval vectervalEvalWithPrec 5 A X
#eval IsolateRoots 10 A (Y' A) X 9
#eval! IsolateRoots 10 A (Y' A) X' 9
end KrawczykTesting
