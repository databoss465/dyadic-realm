import Krawcheck.DyadicIntervals.Basic
import Krawcheck.DyadicIntervals.Vectervals
import Krawcheck.PolynomialBounds
import Krawcheck.MvPolynomials
import Krawcheck.Krawczyk
import Krawcheck.Syntax
import Lean

set_option linter.style.commandStart false
-- set_option linter.style.nativeDecide false
set_option linter.style.longLine false

open Lean Meta Elab Tactic

def Y_default {n : Nat} (S : System (n + 1) (n + 1)) (V : Vecterval (n + 1)) :=
  (Matrival.ApproxInvWithPrec 10 (System.jacobianEvalWithPrec 10 S V)).rat_midpoint

theorem krawcheck_has_root {n : ℕ} {S : System (n + 1) (n + 1)} {V : Vecterval (n + 1)} (prec : Int)
  (max_depth : Nat) : 0 < (Vecterval.IsolateRoots prec S (Y_default S) V max_depth 0).1.length → V.HasRoot S := by
  intro h
  apply Vecterval.isolate_roots_of_has_root _ _ _ _ _ _ h

theorem krawcheck_has_unique_root {n : ℕ} {S : System (n + 1) (n + 1)} {V : Vecterval (n + 1)} (prec : Int)
  (max_depth : Nat) : (Vecterval.IsolateRoots prec S (Y_default S) V max_depth 0).1.length = 1 →
  (Vecterval.IsolateRoots prec S (Y_default S) V max_depth 0).2.length = 0 → V.HasUniqueRoot S := by
  intro h₁ h₂
  apply Vecterval.isolate_roots_of_unique_root' _ _ _ _ _ _ h₁ h₂

theorem krawcheck_has_no_root {n : ℕ} {S : System (n + 1) (n + 1)} {V : Vecterval (n + 1)} (prec : Int)
  (max_depth : Nat) : (Vecterval.IsolateRoots prec S (Y_default S) V max_depth 0) = ([], []) → V.HasNoRoot S := by
  intro h
  apply Vecterval.isolate_roots_empty_of_has_no_roots _ _ _ _ _ _ h

macro "apply_and_decide" t:term : tactic =>
  `(tactic| apply $t <;> native_decide)
  -- `(tactic| apply $t <;> decide +kernel)

def krawcheckGridSearch (thmIdent : Ident) (precs : List Int) (depths : List Nat) : TacticM Unit := do
  let s₀ ← saveState
  for depth in depths do
    for prec in precs do
      let s ← saveState
      dbg_trace s!"[krawcheck] Trying prec={prec}, depth={depth}..."
      try
        let precLit := Syntax.mkNumLit (toString prec)
        let depthLit := Syntax.mkNumLit (toString depth)
        evalTactic <|
          ← `(tactic| apply_and_decide $thmIdent $precLit $depthLit)
        if (← getGoals).isEmpty then
          return
        else
          restoreState s
      catch _ =>
        dbg_trace s!"[krawcheck] failed with prec={prec}, depth={depth}..."
        restoreState s
  restoreState s₀
  throwError m!"Grid Search for krawcheck failed"

elab "krawcheck" : tactic =>
  withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let fn := type.getAppFn
  let precs : List Int := [4, 6, 8, 10, 12, 16]
  let depths : List Nat := [7, 8, 9, 10, 11]
  let s₀ ← saveState
  match fn with
  | .const ``Vecterval.HasRoot _ =>
    krawcheckGridSearch (mkIdent ``krawcheck_has_root) precs depths
  | .const ``Vecterval.HasUniqueRoot _ =>
     krawcheckGridSearch (mkIdent ``krawcheck_has_unique_root) precs depths
  | .const ``Vecterval.HasNoRoot _ =>
     krawcheckGridSearch (mkIdent ``krawcheck_has_no_root) precs depths
  | _ =>
    restoreState s₀
    throwError "krawcheck failed: Goal must be HasRoot, HasNoRoot, or HasUniqueRoot"

-- Make new lean_lib in lakefile.toml and move testing there
-- GuardMsgs for all evals... Remove evals from mail lib
