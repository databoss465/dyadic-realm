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


namespace Vecterval
section VectervalAddendum
open MvRatPol Vecterval System
variable {m n : ℕ} (prec : ℤ)(p : MvRatPol n) (S : System m n) (X Y : Vecterval n)

def HasRoot' := ∃ x ∈ X, (toMvRealPoly p).eval x.get = 0
def HasUniqueRoot' := ∃! x ∈ X, (toMvRealPoly p).eval x.get = 0
def HasNoRoot' := ∀ x ∈ X, (toMvRealPoly p).eval x.get ≠ 0

def HasRoot := ∃ x ∈ X, S.eval x = 0
def HasUniqueRoot := ∃! x ∈ X, S.eval x = 0
def HasNoRoot := ∀ x ∈ X, S.eval x ≠ 0

theorem hasNoRoot_iff_not_hasRoot : X.HasNoRoot S ↔ ¬ X.HasRoot S := by grind only [HasRoot, HasNoRoot]

theorem hasRoot_of_hasUniqueRoot (h : X.HasUniqueRoot S) : X.HasRoot S := by
  simp only [HasUniqueRoot, HasRoot] at *
  apply ExistsUnique.exists; exact h

theorem has_no_root_subset (h : X ⊆ Y) (h': Y.HasNoRoot S) : X.HasNoRoot S := by sorry

theorem subset_has_root (h : X ⊆ Y) (h' : X.HasRoot S) : Y.HasRoot S := by sorry

theorem no_root_of_eval_zerofree (h : ZeroFree (S.vectervalEvalWithPrec prec X)) : X.HasNoRoot S := by sorry

theorem haszero_of_eval (h : X.HasRoot S) : HasZero (S.vectervalEvalWithPrec prec X) := by sorry

end VectervalAddendum
end Vecterval

namespace Vecterval
section KrawczykMethod
open Dyadic DyadicInterval Vecterval Matrival MvRatPol System
variable (prec : ℤ) {n m : ℕ} (S : System m n)
-- If required, pass Y as an argument for later convenience
def Krawczyk (V : Vecterval n) : Vecterval n :=
  let fVm := S.evalWithPrec prec V.midpoint_rat
  let JX := jacobianEvalWithPrec prec S V
  let Y := ApproxInvWithPrec prec JX
  -- let I := @Matrival.one n
  -- Vm - Y * fVm + (I - Y * JX) * (V - Vm)
  V - Y * (fVm + JX * (V - (V.midpoint : Vecterval n)))

-- g(y) = y - Yf(y) => g'(y) = I - Yf'(y)

-- noncomputable def pointwiseKrawczyk (S : System m n) (Y : Matrix (Fin n) (Fin m) ℚ) : System n n :=
--   Vector.ofFn (fun (i : Fin n) ↦ X i - (Vector.ofFn (fun j ↦ Y i j • S.get j)).sum)

-- noncomputable def pointwiseKrawczyk (S : System m n) (Y : Matrix (Fin n) (Fin m) ℚ) : System n n :=
--   Vector.ofFn (fun (i : Fin n) ↦ X i - (∑ j, Y i j • S.get j))

noncomputable def ptwsKrawczyk (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ) (v : Fin n → ℝ) : Fin n →  ℝ :=
  -- X.eval' v - (Y.mulVecᵣ (S.eval' v))
  v - Y.mulVec (S.eval' v)

-- noncomputable def ptwsKrawczyk' (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) : Vector ℝ n :=
--   Vector.ofFn (ptwsKrawczyk S Y x)

-- theorem krawczyk_mvt (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ) (V : Vecterval n) : ∀ v ∈ V, ∀ i,
--   ptwsKrawczyk S Y v.get i = V.midpoint_real.get i + Y.mulVecᵣ (S.eval' V.midpoint_real.get) i
--   1 - Y * J(X)
--   := sorry

theorem krawczyk_sound (S : System m n) (V : Vecterval n) : ∀ v ∈ V,
  Vector.ofFn (ptwsKrawczyk S (ApproxInverse (jacobianEvalWithPrec prec S V)) v.get) ∈ Krawczyk prec S V := by
  generalize h : (jacobianEvalWithPrec prec S V).ApproxInverse = Y
  simp only [mem_iff]
  intro v hv i
  simp only [ptwsKrawczyk, Vector.get_ofFn, Pi.sub_apply]
  simp only [Krawczyk, Vector.get_eq_getElem, Vector.getElem_sub]
  generalize h' : ApproxInvWithPrec prec (jacobianEvalWithPrec prec S V) = Y'
  apply sub_sound
  · simp only [← Vector.get_eq_getElem, hv]
  · have : Y' * (System.evalWithPrec prec S (V.midpoint_rat) +
        jacobianEvalWithPrec prec S V * (V - ofVecDyadic V.midpoint)) = Y'.mulVec (System.evalWithPrec prec S (V.midpoint_rat) +
        jacobianEvalWithPrec prec S V * (V - ofVecDyadic V.midpoint)) := by rfl
    rw [this]; clear this
  -- · change Y.mulVec (S.eval' v.get) i ∈ (Y'.mulVec (System.evalWithPrec prec S (V.midpoint_rat) + jacobianEvalWithPrec prec S V * (V - ofVecDyadic V.midpoint)))[↑i]
    simp only [mulVec, getElem_ofFn, Fin.eta]
    apply mulVec_sound'
    · rw [← h, ← h']
      apply approx_inverse_mem

    · simp only [mem_iff, Vector.get_ofFn]; intro j
      obtain ⟨ξ, hξ, hξ'⟩:= mvt_real_sys S V v hv j
      rw [eval', hξ']; clear hξ'
      simp only [Vecterval.get_add]
      apply add_sound

      · have h₁ := System.eval_sound prec S V.midpoint_rat
        simp only [midpoint_real]
        simp only [eval, mem_iff, Vector.get_ofFn] at h₁
        exact h₁ j

      · have : (v.get - V.midpoint_real.get) = (v - V.midpoint_real).get := by
          ext i; simp only [Pi.sub_apply]
          change v.get i - V.midpoint_real.get i = (Vector.sub v V.midpoint_real).get i
          simp only [Vector.get_eq_getElem, Vector.sub, Vector.getElem_zipWith]
        rw [this]
        apply jacobian_sound
        · exact hξ
        · simp only [mem_iff, get_sub, Pi.sub_apply]; intro k
          rw [← this]
          apply sub_sound
          · apply hv
          · simp only [midpoint_real, Vector.get_map, ofVecDyadic, midpoint_rat, to_rat_mem_of_dyadic]

def ptwsKrawczykFDeriv (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ)
  (f : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] Fin n → ℝ := by
  sorry

theorem ptws_krawczyk_fderiv (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ)
  (V : Vecterval n) : ∀ x ∈ V.toSet, HasFDerivWithinAt
  (ptwsKrawczyk S Y) (ptwsKrawczykFDeriv S Y x) V.toSet x := by
  sorry

-- theorem ptws_krawczyk_mvt (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ) (V : Vecterval n)
--   (y : Fin n → ℝ) : ∀ x ∈ V, ∃ ξ,
--   (ptwsKrawczyk S Y x.get) = (ptwsKrawczyk S Y V.midpoint_real.get) +
--   ptwsKrawczykFDeriv S Y ξ y := by sorry

theorem ptws_krawczyk_mapsTo (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ) (V : Vecterval n) :
  Set.MapsTo (ptwsKrawczyk S Y) V.toSet V.toSet := by
  simp only [Set.mapsTo_iff_image_subset, Set.image_subset_iff]
  intro x hx; simp only [Set.mem_preimage]
  sorry

instance (K : NNReal) (Y : Matrix (Fin n) (Fin m) ℝ) : ContractingWith K (ptwsKrawczyk S Y) where
  left := sorry -- Get this from isValidKrawczyk
  right := sorry -- Get this using Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le

variable (Y : Matrix (Fin n) (Fin m) ℝ) (V : Vecterval n)

#check ptwsKrawczyk S Y
#check Set.mapsTo_iff_image_subset
#check @Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (Fin n → ℝ) _ _ ℝ (Fin n → ℝ) _ _ _ _ _ (ptwsKrawczyk S Y) V.toSet _ 1    (ptws_krawczyk_fderiv S Y V) _ V.convex
#check LipschitzOnWith.to_restrict
#check @ContractingWith.exists_fixedPoint' (Fin n → ℝ) _ 1 (ptwsKrawczyk S Y) _ (complete V) (ptws_krawczyk_mapsTo S Y V)

/-- Jacobian of system evaluated on the interval is non-singular and Krawczyk map is contractive -/
def isValidKrawczyk (V : Vecterval n) :=
  let J := jacobianEvalWithPrec prec S V
  let J' := J.rat_midpoint
  let Y := ApproxInvWithPrec prec J
  let I := @Matrival.one n
  ((J'.transpose * J').det ≠ 0) ∧ Matrival.norm (I - Y * J) < 1
instance (V : Vecterval n) : Decidable (isValidKrawczyk prec S V) := by
  simp only [isValidKrawczyk]; infer_instance

def IsolateRoots (prec : ℤ) {n m : ℕ} (S : System m (n + 1)) (V : Vecterval (n + 1))
  (max_depth : ℕ) (min_width: Dyadic) : List (Vecterval (n + 1)) × List (Vecterval (n + 1)) :=
  if (S.vectervalEvalWithPrec prec V).ZeroFree then ([], [])
    else if isValidKrawczyk prec S V then
      let J := jacobianEvalWithPrec prec S V
      let Y :=ApproxInvWithPrec prec J
      let K := V.Krawczyk prec S
      match V ⊓ K with
      | none => ([], [])
      | some Z => if K ⊆ V then ([V], [])
          else if (Z.maxWidth ≤ min_width) ∨ (max_depth = 0) then ([],[V])
          else IsolateRoots prec S Z (max_depth - 1) (min_width)
    else if max_depth = 0 then ([],[V])
    else let (L, R) := V.split_along (V.maxWidthIdx)
    let rL := IsolateRoots prec S L (max_depth - 1) (min_width)
    let rR := IsolateRoots prec S R (max_depth - 1) (min_width)
    (rL.1 ++ rR.1, rL.2 ++ rR.2)

end KrawczykMethod
end Vecterval
