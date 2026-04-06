import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.PolynomialBounds
import DyadicRealm.DyadicIntervals.Vectervals
import DyadicRealm.DyadicIntervals.MvPolynomials
import DyadicRealm.DyadicIntervals.Krawczyk
import DyadicRealm.DyadicIntervals.Syntax
import Lean
open Rat Lean Meta Elab Tactic


syntax (name := krawcheck) "krawcheck" : tactic

def V₀ : Vecterval 2 := #v[dy[[0,1/2]], dy[[0,1]]]
def V₁ : Vecterval 2 := #v[dy[[-1,0]], dy[[0,1]]]
def V₂ : Vecterval 2 := #v[dy[[3/2, 2]], dy[[-5/2, 2]]]
def S : System 2 2 := poly[x1 ^ 2, -2 / 3 * x1, x2 ^ 2, -8/9 ; -1 * x1, x2 ^ 2, -2/3]

example : -1 ≤ 2 := by valid_endpts
example : toDyadic (-1/2) 2 ≤ 2 := by valid_endpts
example : toDyadic (-3/2) 2 ≤ -1 := by valid_endpts
example : toDyadic (-3/2) 2 ≤ toDyadic (-1/2) 2 := by valid_endpts
example : toDyadic (3/2) 2 ≤ 5 := by valid_endpts

example : -1 ≤ toDyadic (3/2) 2 := by valid_endpts

example : -1 ≤ toDyadic (-1/2) 2 := by valid_endpts

example : V₀.HasRoot S := by sorry

example : V₁.HasNoRoot S := by sorry

example : V₂.HasUniqueRoot S := by sorry

#eval toDyadic (-1/5) 5
