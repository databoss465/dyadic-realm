import Mathlib
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
import DyadicRealm.DyadicIntervals.Division
import DyadicRealm.DyadicIntervals.PolynomialBounds
import DyadicRealm.DyadicIntervals.PolynomialRoots
import DyadicRealm.DyadicIntervals.Vectervals
import DyadicRealm.DyadicIntervals.MvPolynomials

-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false


namespace Krawczyk
section Krawczyk
open Dyadic DyadicInterval Vecterval Matrival MvRatPol
variable (prec : ℤ) {n m : ℕ} (S : System m n) (X : Vecterval n)

-- Passing Y as an argument for later convenience
def krawczyk (Y : Matrival n m) : Vecterval n :=
  let Xm : Vecterval n := X.midpoint
  let fXm := sysEvalWithPrec prec S (X.midpoint.map toRat)
  let JX := jacobianEvalWithPrec prec S X
  -- let Y := ApproxInvWithPrec prec JX
  let I := @Matrival.one n
  Xm - Y * fXm + (I - Y * JX) * (X - Xm)

def isValidKrawczyk :=
  let J := jacobianEvalWithPrec prec S X
  let J' := J.rat_midpoint
  let Y := ApproxInvWithPrec prec J
  let I := @Matrival.one n
  ((J'.transpose * J').det ≠ 0) ∧ Matrival.norm (I - Y * J) < 1
instance : Decidable (isValidKrawczyk prec S X) := by
  simp only [isValidKrawczyk]; infer_instance

def IsolateRoots (prec : ℤ) {n m : ℕ} (S : System m (n + 1)) (X : Vecterval (n + 1))
  (max_depth : ℕ) (min_width: Dyadic) : List (Vecterval (n + 1)) × List (Vecterval (n + 1)) :=
  if (sysVectervalEvalWithPrec prec S X).ZeroFree then ([], [])
    else if isValidKrawczyk prec S X then
      let J := jacobianEvalWithPrec prec S X
      let Y :=ApproxInvWithPrec prec J
      let K := krawczyk prec S X Y
      match X ⊓ K with
      | none => ([], [])
      | some Z => if K ⊆ X then ([X], [])
          else if (Z.maxWidth ≤ min_width) ∨ (max_depth = 0) then ([],[X])
          else IsolateRoots prec S Z (max_depth - 1) (min_width)
    else if max_depth = 0 then ([],[X])
    else let (L, R) := X.split_along (X.maxWidthIdx)
    let rL := IsolateRoots prec S L (max_depth - 1) (min_width)
    let rR := IsolateRoots prec S R (max_depth - 1) (min_width)
    (rL.1 ++ rR.1, rL.2 ++ rR.2)


end Krawczyk
end Krawczyk
