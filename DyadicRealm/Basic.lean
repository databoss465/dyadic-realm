import DyadicRealm.DyadicIntervals
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

def Y (S : System 2 2)(X : Vecterval 2) := (ApproxInvWithPrec 10 (jacobianEvalWithPrec 10 S X)).rat_midpoint

-- Circle and Parabola
def J₁ : DyadicInterval := ⟨(toDyadic (-5/2) 2), (toDyadic (5/2) 2), (by sorry)⟩  --[[-5/2, 5/2]]
def J₂ : DyadicInterval := ⟨(toDyadic (-5/2) 2), 2, (by sorry)⟩                   -- [[-5/2, 2]]
-- def V : Vecterval 2 := #v[J₁, J₂]
def V : Vecterval 2 := #v[⟨-5,5, by decide⟩, ⟨-5, 5, by decide⟩]                   --[[-5, 5]] × [[-5, 5]]

def q₁ : MvRatPol 2 := [(1, #v[2, 0]), (1, #v[0, 2]), (-5, #v[0, 0])]     -- x1^2 + x2^2 - 5
def q₂ :  MvRatPol 2 := [(1, #v[2, 0]), (-1, #v[0, 1]), (-3, #v[0, 0])]   -- x1^2 - x2 - 3
def S : System 2 2 := #v[q₁, q₂]

#eval! vectervalEvalWithPrec 5 S V
#eval! isValidKrawczyk 10 S (Y S V) V

-- At prec 5 and max_depth 10, finds all 4 roots
-- For smaller intervals, we need less depth to find the roots
#eval! (IsolateRoots 10 S (Y S) V 10 0)

-- Another 2x2 System
-- 2 Roots: [[0, 0.5]] × [[0, 0.5]], [[0, 0.5]] × [[0.5, 1]]
-- Also has a root in [[1, 2]] × [[-2, -3]]

def V₀ : Vecterval 2 := #v[⟨0,(toDyadic (1/2) 2), by sorry⟩, ⟨0,1, by grind⟩]   -- [[0, 1/2]] × [[0, 1]]
def V₁ : Vecterval 2 := #v[⟨-1,0, by grind⟩, ⟨0,1, by grind⟩]                   -- [[-1, 0]] × [[0, 1]]
def V₂ : Vecterval 2 := #v[⟨(toDyadic (3/2) 2),2,by sorry⟩,
  ⟨(toDyadic (-5/2) 2), -2, by sorry⟩]                                         --[[3/2, 2]], [[-5/2, -2]]


def s₁ : MvRatPol 2 := [(4, #v[2, 1]), (9/4, #v[1,2]),
  (-1/2, #v[1, 0]), (-5/2, #v[0,1]), (1, #v[0,0])] -- 4 * x1^2 * x2 + 9/4 * x1 * x2^2 - 1/2 * x1 - 5/2 * x2 + 1
def s₂ : MvRatPol 2 := [(1, #v[3, 0]), (1, #v[0, 3]), (-3/2, #v[1, 1])] -- x1^3 + x2^3 - 3/2 * x1 * x2
def S₀ : System 2 2 := #v[s₁, s₂]

#eval! evalWithPrec 5 S₀ #v[1, 1]
#eval! vectervalEvalWithPrec 5 S₀ V₀
#eval! isValidKrawczyk 10 S₀ (Y S₀ V₁) V₁

#eval! (IsolateRoots 7 S₀ (Y S₀) V₀ 10 0)  -- Finds both roots!
#eval (IsolateRoots 4 S₀ (Y S₀) V₁ 6 0)    -- Certifies No roots!
#eval! (IsolateRoots 10 S₀ (Y S₀) V₂ 4 0)  -- Certifies One root!



end KrawczykTesting
