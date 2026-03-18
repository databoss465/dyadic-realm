import DyadicRealm.DyadicIntervals

section NewtonTesting
open Rat DyadicInterval RatPol

def I : DyadicInterval := ⟨1, (toDyadic ((7 : ℚ)/(2 : ℚ)) 5), (by sorry)⟩
def p : RatPol 3 := #v[2, -4, 1] -- x^2 - 4x + 2
#eval! IsolateRoots I p 5 5 0

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
open Vecterval MvRatPol

end KrawczykTesting
