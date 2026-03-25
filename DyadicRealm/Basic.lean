import DyadicRealm.DyadicIntervals
import Lean
open Lean Elab Term Meta

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
def I₁ : DyadicInterval := ⟨(toDyadic ((-1 : ℚ)/(2 : ℚ)) 2), 2 , (by sorry)⟩ --[[-1/2, 2]]
def p₁ : RatPol 3 := #v[-1, 0, 1] -- x^2 - 1
#eval! IsolateRoots I₁ p₁ 6 5 0 --([[[3/4, 2]]], [])

-- Case 2
def I₂ : DyadicInterval := ⟨(toDyadic ((-1 : ℚ)/(2 : ℚ)) 2), 1 , (by sorry)⟩ -- [[-1/2, 1]]
def p₂ : RatPol 4 := #v[0, 0, 0, 1] -- x^3
#eval! IsolateRoots I₂ p₂ 5 5 0 -- ([], [[[-1/32, 1/64]]])

-- Case 3
def I₃ : DyadicInterval :=
  ⟨(toDyadic ((5 : ℚ)/(4 : ℚ)) 2), (toDyadic ((3 : ℚ)/(2 : ℚ)) 2), (by sorry)⟩ -- [5/4, 3/2]
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

-- Circle and Parabola
def J₁ : DyadicInterval := ⟨(toDyadic ((-5 : ℚ)/(2 : ℚ)) 2),
  (toDyadic ((5 : ℚ)/(2 : ℚ)) 2), (by sorry)⟩
  -- With the interval [[-5/2, 5/2]], all 4 roots are detected
def J₂ : DyadicInterval := ⟨(toDyadic ((-5 : ℚ)/(2 : ℚ)) 2), 2, (by sorry)⟩ -- [[-5/2, 2]]
def V : Vecterval 2 := #v[J₁, J₂]

def q₁ : MvRatPol 2 := [(1, #v[2, 0]), (1, #v[0, 2]), (-5, #v[0, 0])] -- x1^2 + x2^2 - 5
def q₂ :  MvRatPol 2 := [(1, #v[2, 0]), (-1, #v[0, 1]), (-3, #v[0, 0])] -- x1^2 - x2 - 3
def S : System 2 2 := #v[q₁, q₂]

def Y (X : Vecterval 2) := (ApproxInvWithPrec 10 (jacobianEvalWithPrec 10 S X)).rat_midpoint
def Y' (X : Vecterval 2) := (ApproxInvWithPrec 10 (jacobianEvalWithPrec 10 S X))
#eval! (Matrival.ofRatWithPrec 10 (Y V))[0] ⊆ (Y' V)[0]
#eval! (Y V).det ≠ 0
#eval! (jacobianEvalWithPrec 10 S V)
#eval! Matrival.norm (Matrival.one - (Y' V) * (jacobianEvalWithPrec 10 S V)) < 1

#eval! vectervalEvalWithPrec 5 S V
#eval! isValidKrawczyk 10 S (Y V) V
-- At max_depth 13, finds all 4 roots
-- For smaller intervals, we need less depth to find the roots
#eval! (IsolateRoots 4 S Y V 13 0)

-- Another 2x2 System

end KrawczykTesting
