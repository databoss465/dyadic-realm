import Mathlib
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.PolynomialBounds
import DyadicRealm.DyadicIntervals.Vectervals
import DyadicRealm.DyadicIntervals.MvPolynomials
import Lean

section PolyNomialSyntax
open Lean Elab Term Meta Macro Command
declare_syntax_cat mono_var
--Identifier with an optional numerical exponent is a monomial variable
syntax ident (" ^ " num)? : mono_var

declare_syntax_cat strict_mono
-- A number with an optional negative sign and denominator can be a monomial
declare_syntax_cat coeff
syntax "-"? num (" / " num)? : coeff
syntax coeff : strict_mono
-- A sequence of variables separated by * can be a monomial
-- Includes sequence of 1 var without any separators also
declare_syntax_cat vars
syntax sepBy1(mono_var, " * ") : vars
syntax vars : strict_mono

-- An optional coefficient followed by a chain of variables can be a monomial
syntax coeff " * " vars : strict_mono


declare_syntax_cat poly
-- poly is one one or more comma-sep strict_mono's
syntax strict_mono,+ : poly
-- the term called system is one or more semicolo-sep poly's
-- syntax (name := polynomial) "poly[" strict_mono,+ "]" : term
syntax (name := system) "poly[" sepBy1(poly, ";")"]" : term

/-- Counts the maximum index of variables in a monomial of syntax category term -/
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

/-- Counts the maximum index of variables in a monomial of any syntax category -/
partial def countMonoVar' (stx : Syntax) : MacroM Nat := do
  match stx with
  | `($id:ident) => do
        let name := id.getId.toString
        if name.startsWith "x" then
          let numStr := name.drop 1
          match numStr.toNat? with
          | some n => return n
          | none => Macro.throwErrorAt id "Variable index must be a number"
        else return 0
  | _ =>
    let mut maxIdx := 0
    for child in stx.getArgs do
      let childMax ← countMonoVar' child
      maxIdx := max maxIdx childMax
    return maxIdx

partial def countVar (stx : Syntax) : MacroM Nat := do
  match stx with
  | `(poly[ $m:strict_mono,* ]) =>
    let mut overallMax := 0
    for mono in m.getElems do
      let monoMax ← countMonoVar' mono
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
      let maxIdx ← liftMacroM (countMonoVar' t)
      logInfo m!"{maxIdx}"

#test_count 4 * x1 ^ 3 * x2 ^ 2
#test_count - 5/7 * x3
#test_count 2/3

#test_count poly[x1 ^ 2, x2 ^ 2, x3 ^ 2, -3]
#test_count poly[4 * x1, x2 ; 3 * x3 ^ 2, -1 * x2^2; x2, -5]

partial def updateVec (n : Nat) (vec : Vector (TSyntax `num) n)
  (stx : Syntax) : MacroM (Vector (TSyntax `num) n) := do
  match stx with
  | `($a * $b) =>
    let vec1 ← updateVec n vec a
    updateVec n vec1 b
  | `($id:ident ^ $a:num) =>
    let name := id.getId.toString
    if name.startsWith "x" then
      let idx := name.drop 1
      match idx.toNat? with
      | some 0 => Macro.throwErrorAt id "Variable indexing begins from 1"
      | some (m + 1) =>
        if m < n then
          return vec.set! m a
        else Macro.throwErrorAt id s!"Index out of bounds! Dimension is {n}."
      | none => Macro.throwErrorAt id "Variable index must be a valid number"
    else Macro.throwErrorAt id "Variables must start with `x`"
  | `($id:ident) =>
    let name := id.getId.toString
    if name.startsWith "x" then
      let idx := name.drop 1
      match idx.toNat? with
      | some 0 => Macro.throwErrorAt id "Variable indexing begins from 1"
      | some (m + 1) =>
        if m < n then
          let one ← `(num|1)
          return vec.set! m one
        else Macro.throwErrorAt id s!"Index out of bounds! Dimension is {n}."
      | none => Macro.throwErrorAt id "Variable index must be a valid number"
    else Macro.throwErrorAt id "Variables must start with `x`"
  | _ => Macro.throwError "Expected valid identifier like x1, x2, etc."

def updateVec' (n : Nat) (vec : Vector (TSyntax `num) n)
  (stx : TSyntax `vars) : MacroM (Vector (TSyntax `num) n) := do
  let mut currentVec := vec
  for child in stx.raw[0].getArgs do
    match child with
    -- xi ^ a
    | `(mono_var| $id:ident ^ $a:num) =>
      let name := id.getId.toString
      if name.startsWith "x" then
        let idx := name.drop 1
        match idx.toNat? with
        | some 0 => Macro.throwErrorAt id "Variable indexing begins from 1"
        | some (m + 1) =>
          if m < n then
            currentVec := currentVec.set! m a
          else Macro.throwErrorAt id s!"Index out of bounds! Dimension is {n}."
        | none => Macro.throwErrorAt id "Variable index must be a valid number"
      else Macro.throwErrorAt id "Variables must start with `x`"
    -- xi
    | `(mono_var| $id:ident) =>
      let name := id.getId.toString
      if name.startsWith "x" then
        let idx := name.drop 1
        match idx.toNat? with
        | some 0 => Macro.throwErrorAt id "Variable indexing begins from 1"
        | some (m + 1) =>
          if m < n then
            let one ← `(num|1)
            currentVec := currentVec.set! m one
          else Macro.throwErrorAt id s!"Index out of bounds! Dimension is {n}."
        | none => Macro.throwErrorAt id "Variable index must be a valid number"
      else Macro.throwErrorAt id "Variables must start with `x`"
    -- Explicitly ignore the "*" tokens
    | _ => pure ()
  return currentVec

/-- Convert a `coeff` syntax node into a `term` that elaborates as a rational number -/
def coeffToTerm (c : TSyntax `coeff) : MacroM (TSyntax `term) := do
  match c with
  -- -a/b
  | `(coeff| - $a:num / $b:num) =>
    `(-(($a : ℚ) / $b))
  -- a/b
  | `(coeff| $a:num / $b:num) =>
    `(($a : ℚ) / $b)
  -- -a
  | `(coeff| - $a:num) =>
    `(-($a : ℚ))
  -- a
  | `(coeff| $a:num) =>
    `(($a : ℚ))
  | _ => Macro.throwErrorAt c "Unrecognized coefficient format"

partial def buildMono (n : Nat) (stx : TSyntax `strict_mono) :
  MacroM (TSyntax `term) := do
  let zero ← `(num| 0)
  let one ← `(num| 1)
  let initVec := Vector.replicate n zero
  match stx with
  | `(strict_mono| $c:coeff) =>
    let ct ← coeffToTerm c
    `(($ct, #v[ $(initVec.toArray),* ]))
  | `(strict_mono| $x:vars) =>
    let vec ← updateVec' n initVec x
    `(($(⟨one⟩), #v[ $(vec.toArray),* ]))
  | `(strict_mono| $c:coeff * $x:vars) =>
    let ct ← coeffToTerm c
    let vec ← updateVec' n initVec x
    `(($ct, #v[ $(vec.toArray),* ]))
  | _ => Macro.throwErrorAt stx "Unrecognized strict_mono format."

partial def buildPoly (stx : TSyntax `poly) :
  MacroM (TSyntax `term) := do
  let n ← countVar (← `(poly[ $stx:poly ]))
  match stx with
  | `(poly| $monos:strict_mono,*) =>
    let mut termArray := #[]
    for mono in monos.getElems do
      let term ← buildMono n mono
      termArray := termArray.push term
    `([$(termArray),*])
  | _  => Macro.throwError "Invalid polynomial syntax"

partial def buildPoly' (n : Nat)(stx : TSyntax `poly) :
  MacroM (TSyntax `term) := do
  match stx with
  | `(poly| $monos:strict_mono,*) =>
    let mut termArray := #[]
    for mono in monos.getElems do
      let term ← buildMono n mono
      termArray := termArray.push term
    `([$(termArray),*])
  | _  => Macro.throwError "Invalid polynomial syntax"

partial def buildSystem (stx : TSyntax `term) :
  MacroM (TSyntax `term) := do
  let (_, n) ← countDim stx
  match stx with
  | `(poly[ $sys:poly;* ]) =>
    let mut termArray := #[]
    for p in sys.getElems do
      let term ← buildPoly' n p
      termArray := termArray.push term
    `(#v[$(termArray),*])
  | _ => Macro.throwError "Invalid system syntax"

elab "#test_update" n:num " : " t:vars : command => do
   liftTermElabM do
    let zero ← `(num| 0)
    let initVec := Vector.replicate n.getNat zero
    let vec ← liftMacroM (updateVec' n.getNat initVec t)
    let result ← liftMacroM `(#v[ $(vec.toArray),*])
    logInfo m!"{result}"

elab "#test_mono" n:num " : " t:strict_mono : command => do
  liftTermElabM do
    let result ← liftMacroM (buildMono n.getNat t)
    logInfo m!"{result}"

elab "#test_poly" t:poly : command => do
  liftTermElabM do
  let result ← liftMacroM (buildPoly t)
  logInfo m!"{result}"

#test_update 5 : x1 * x2 ^ 2 * x5 ^ 7
#test_mono 5 : -4/3 * x1^2 * x2
#test_poly -4/3 * x1^2 * x2, 3 * x4 ^ 2, -2*x3 * x2

macro_rules
  | `(poly[ $p:poly ]) => buildPoly p
  | `(poly[ $p:poly;* ]) => do buildSystem (← `(poly[ $p;* ]))

#eval poly[x1^2, x2^2, x3^2, -3]
#eval poly[4 * x1, x2 ; 3 * x3 ^ 2, -1 * x2^2; x2, -5]

end PolyNomialSyntax

section DyadicSyntax
open Lean Meta Elab Tactic

macro "valid_endpts" : tactic => `(tactic|
  first
  | rw [← Dyadic.toRat_le_toRat_iff]
    try rw[Dyadic.toRat_neg]
    try rw [Dyadic.toRat_ofNat]
    simp only [Rat.toRat_toDyadic, Rat.floor, Int.cast_ite]
    ring_nf;grind
  | grind only [Rat.toDyadic_mono]
  | norm_cast
  )

declare_syntax_cat endpt
syntax "dy[[" coeff "," coeff "]]" : term

def getPrec (c : TSyntax `coeff) : MacroM Nat := do
  match c with
  | `(coeff| - $_:num / $b:num) | `(coeff| $_:num / $b:num) =>
    let prec := b.getNat.log2
    if b.getNat = 2 ^ prec then return prec
    else Macro.throwErrorAt c s!"Denominator {b.getNat} is not a power of 2"
  | `(coeff| - $_) | `(coeff| $_) =>
    return 0

def coeffToDyadicWithPrec (c : TSyntax `coeff) (prec : Nat) :
  MacroM (TSyntax `term) := do
  let precStx := Syntax.mkNumLit (toString prec)
  match c with
  | `(coeff| - $a:num / $b:num) =>  `(Rat.toDyadic (-$a / $b) $precStx)
  | `(coeff| $a:num / $b:num)   =>  `(Rat.toDyadic ($a / $b) $precStx)
  | `(coeff| - $a:num)          =>  `(-$a)
  | `(coeff| $a:num)            =>  `($a)
  | _ => Macro.throwErrorAt c "Invalid dyadic"

macro_rules
  | `(dy[[ $a:coeff , $b:coeff]]) => do
    let precA ← getPrec a
    let precB ← getPrec b
    let prec := max precA precB
    let aTerm ← coeffToDyadicWithPrec a prec
    let bTerm ← coeffToDyadicWithPrec b prec
    `(DyadicInterval.mk $aTerm $bTerm (by valid_endpts))

end DyadicSyntax

example : -1 ≤ 2 := by valid_endpts
example : Rat.toDyadic (-1/2) 2 ≤ 2 := by valid_endpts
example : Rat.toDyadic (-3/2) 2 ≤ -1 := by valid_endpts

example : Rat.toDyadic (-3/4) 2 ≤ Rat.toDyadic (3/4) 2 := by valid_endpts
  -- grind only [Rat.toDyadic_mono]

example : Rat.toDyadic (3/2) 2 ≤ 5 := by valid_endpts
  -- rw [← Dyadic.toRat_le_toRat_iff]
  -- try rw[Dyadic.toRat_neg]
  -- try rw [Dyadic.toRat_ofNat]
  -- simp only [Rat.toRat_toDyadic, Rat.floor, Int.cast_ite]
  -- ring_nf;grind

example : -1 ≤ Rat.toDyadic (3/2) 2 := by valid_endpts
  -- rw [← Dyadic.toRat_le_toRat_iff]
  -- try rw[Dyadic.toRat_neg]
  -- try rw [Dyadic.toRat_ofNat]
  -- simp only [Rat.toRat_toDyadic, Rat.floor, Int.cast_ite]
  -- ring_nf;grind

example : -1 ≤ Rat.toDyadic (-1/2) 2 := by valid_endpts
  -- rw [← Dyadic.toRat_le_toRat_iff]
  -- try rw[Dyadic.toRat_neg]
  -- try rw [Dyadic.toRat_ofNat]
  -- simp only [Rat.toRat_toDyadic, Rat.floor, Int.cast_ite]
  -- ring_nf;grind

example : 0 ≤ Rat.toDyadic (1/2) 1 := by valid_endpts
  -- rw [← Dyadic.toRat_le_toRat_iff]
  -- try rw[Dyadic.toRat_neg]
  -- try rw [Dyadic.toRat_ofNat]
  -- simp only [Rat.toRat_toDyadic, Rat.floor, Int.cast_ite]
  -- ring_nf;grind

#eval dy[[0, 1/2]]
