import Mathlib
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.PolynomialBounds
import DyadicRealm.DyadicIntervals.Vectervals
import DyadicRealm.DyadicIntervals.MvPolynomials
import Lean
open Lean Elab Term Meta Macro Command

declare_syntax_cat poly
syntax term,+ : poly
syntax (name := system) "poly[" sepBy1(poly, ";")"]" : term

partial def countMonoVar (stx : Syntax) : MacroM Nat := do
  match stx with
  | `($id:ident) => do
        let name := id.getId.toString
        if name.startsWith "x" then
          let numStr := name.drop 1
          match numStr.toNat? with
          | some n => return n
          | none => Macro.throwErrorAt id "Variable index must be a number"
        else return 7
  | `($a ^ $_b) =>
    (countMonoVar a)
  | `($a * $b) =>
    let A ← countMonoVar a
    let B ← countMonoVar b
    return max A B
  | `($_:num) =>
    return 0
  | `($a / $b) =>
    let A ← countMonoVar a
    let B ← countMonoVar b
    return max A B
  | `(- $a) =>
    countMonoVar a
  | _ => Macro.throwError s!"Check {stx}"

partial def countVar (stx : Syntax) : MacroM Nat := do
  match stx with
  | `(poly[ $m:term,* ]) =>
    let mut overallMax := 0
    for mono in m.getElems do
      let monoMax ← countMonoVar mono
      overallMax := max overallMax monoMax
    return overallMax
  | _ => Macro.throwError s!"Scanner failed: Expected poly[...] syntax, got {stx}"

partial def countDim (stx : Syntax) : MacroM (Nat × Nat) := do
  match stx with
  | `(poly[ $p:poly;*]) =>
      let mut overallMax := 0
      let dim := p.getElems.size
      for pol in p.getElems do
        let polyMax ← countVar (← `(poly[ $pol:poly ]))
        overallMax := max overallMax polyMax
      return (dim, overallMax)
  | _ => Macro.throwError s!"Scanner failed: Expected poly[...] syntax, got {stx}"

elab "#test_count " t:term : command => do
  liftTermElabM do
    match t with
    | `(poly[$_:poly]) =>
      let n ← liftMacroM (countVar t)
      logInfo m!"{n}"
    | `(poly[$_:poly;*]) =>
      let n ← liftMacroM (countDim t)
      logInfo m!"{n}"
    | _ =>
      let maxIdx ← liftMacroM (countMonoVar t)
      logInfo m!"{maxIdx}"

#test_count 4 * x1 ^ 3 * x2 ^ 2
#test_count - 5/7 * x3
#test_count 2/3

#test_count poly[x1^2, x2^2, x3^2, -3]
#test_count poly[4 * x1, x2 ; 3 * x3 ^ 2, -1 * x2^2; x2, -5]

@[macro system]
def expandSystem : Macro := fun stx ↦ do
  let (m, n) ← countDim stx
  let msgTerm : TSyntax `term := quote s!"This system has {m} equations and {n} variables."
  return msgTerm

#eval poly[x1^2, x2^2, x3^2, -3]
#eval poly[4 * x1, x2 ; 3 * x3 ^ 2, -1 * x2^2; x2, -5]
