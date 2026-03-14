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
-- set_option pp.all true


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

def contractionFactor (V : Vecterval n) : Dyadic :=
  let JX := jacobianEvalWithPrec prec S V
  let Y := ApproxInvWithPrec prec JX
  let I := @Matrival.one n
  (I - Y * JX).norm

def contractionFactor' (V : Vecterval n) : NNReal :=
  let JX := jacobianEvalWithPrec prec S V
  let Y := ApproxInvWithPrec prec JX
  let I := @Matrival.one n
  (I - Y * JX).norm'

-- def isContraction  (V : Vecterval n) : Prop := contractionFactor' prec S V < 1

noncomputable def ptwsKrawczyk (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ) (v : Fin n → ℝ) : Fin n →  ℝ :=
  v - Y.mulVec (S.eval' v)

theorem mem_toSet_iff {n : ℕ} (X : Vecterval n) (f : Fin n → ℝ) : f ∈ X.toSet ↔ (Vector.ofFn f) ∈ X := by
  sorry

theorem krawczyk_sound (S : System m n) (V : Vecterval n) : ∀ v ∈ V,
  (ptwsKrawczyk S (ApproxInverse (jacobianEvalWithPrec prec S V)) v.get) ∈ (Krawczyk prec S V).toSet := by
  generalize h : (jacobianEvalWithPrec prec S V).ApproxInverse = Y
  intro v hv
  rw [mem_toSet_iff]
  simp only [mem_iff]
  intro i
  simp only [ptwsKrawczyk, Vector.get_ofFn, Pi.sub_apply]
  simp only [Krawczyk, Vector.get_eq_getElem, Vector.getElem_sub]
  generalize h' : ApproxInvWithPrec prec (jacobianEvalWithPrec prec S V) = Y'
  apply DyadicInterval.sub_sound
  · simp only [← Vector.get_eq_getElem]
    grind only [mem_iff]
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
          apply DyadicInterval.sub_sound
          · apply hv
          · simp only [midpoint_real, Vector.get_map, ofVecDyadic, midpoint_rat, to_rat_mem_of_dyadic]

noncomputable def ptwsKrawczykFDeriv (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ)
  (f : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
  ContinuousLinearMap.id ℝ (Fin n → ℝ) - (LinearMap.toContinuousLinearMap (Matrix.toLin' Y)).comp
      (ContinuousLinearMap.pi (fun i ↦ (S.get i).fderiv f))

theorem ptws_krawczyk_fderiv_matrix_comp (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ)
  (f : Fin n → ℝ) : ptwsKrawczykFDeriv S Y f = LinearMap.toContinuousLinearMap
  ((1 - Y * (exactJacobian S f))).toLin' := by
  simp only [ptwsKrawczykFDeriv, map_sub, Matrix.toLin'_one, Matrix.toLin'_mul]
  have : ContinuousLinearMap.id ℝ (Fin n → ℝ) = LinearMap.toContinuousLinearMap LinearMap.id := by rfl
  simp only [this, sub_right_inj]
  change (LinearMap.toContinuousLinearMap (Matrix.toLin' Y)).comp (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv f) =
  LinearMap.toContinuousLinearMap (Matrix.toLin' Y ∘ₗ Matrix.toLin' (LinearMap.toMatrix' (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv f).toLinearMap))
  simp only [Matrix.toLin'_toMatrix']; congr

theorem ptws_krawczyk_fderiv (S : System m n) (Y : Matrix (Fin n) (Fin m) ℝ)
  (V : Vecterval n) : ∀ v ∈ V.toSet, HasFDerivWithinAt
  (ptwsKrawczyk S Y) (ptwsKrawczykFDeriv S Y v) V.toSet v := by
  intro v hv
  unfold ptwsKrawczyk ptwsKrawczykFDeriv
  apply HasFDerivWithinAt.sub
  · simp only [hasFDerivWithinAt_pi', ContinuousLinearMap.comp_id]
    intro i; apply hasFDerivWithinAt_apply
  · simp only [hasFDerivWithinAt_pi']; intro i
    -- Rewrite Y * f(x) i as some f ∘ g
    change HasFDerivWithinAt ((fun y ↦ y i) ∘ (fun x ↦ Y.mulVec (S.eval' x))) ((ContinuousLinearMap.proj i).comp
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' Y)).comp
      (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv v))) V.toSet v
    apply HasFDerivWithinAt.comp v (hasFDerivWithinAt_apply _ _ _) _ (Set.mapsTo_univ _ _)
    -- Rewrite Y * f(x) as some f ∘ g
    change HasFDerivWithinAt ((fun y ↦ Y.mulVec y) ∘ (fun x ↦ S.eval' x)) ((LinearMap.toContinuousLinearMap (Matrix.toLin' Y)).comp (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv v)) V.toSet v
    apply HasFDerivWithinAt.comp v _ _ (Set.mapsTo_univ _ _)
    · -- Rewrite (fun y ↦ Y.mulVec y) as a CtsLinMap
      change HasFDerivWithinAt ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' Y)) (LinearMap.toContinuousLinearMap (Matrix.toLin' Y)) Set.univ (S.eval' v)
      apply ContinuousLinearMap.hasFDerivWithinAt
    · grind only [hasFDerivWithinAt_pi', ContinuousLinearMap.proj_pi, eval', hasFDerivWithinAt_eval]

theorem ptws_krawczyk_mapsTo (S : System m n) (V : Vecterval n) (hK : Krawczyk prec S V ⊆ V):
  Set.MapsTo (ptwsKrawczyk S (jacobianEvalWithPrec prec S V).ApproxInverse) V.toSet V.toSet := by
  simp only [Set.mapsTo_iff_image_subset, Set.image_subset_iff]
  intro v hv; simp only [Set.mem_preimage]
  rw [mem_toSet_iff] at hv
  have : v = (Vector.ofFn v).get := by ext i; simp only [Vector.get_ofFn]
  rw [this]
  apply Set.mem_of_mem_of_subset
  · exact (krawczyk_sound prec S V _ hv)
  · grind only [= subset_iff_toSet]

theorem ptws_krawczyk_deriv_norm_le (S : System m n) (V : Vecterval n) : ∀ v ∈ V.toSet,
  ‖ptwsKrawczykFDeriv S (ApproxInverse (jacobianEvalWithPrec prec S V)) v‖₊ ≤ contractionFactor' prec S V := by -- 2 is just a placeholder for proof structure
  intro v hv  --; simp only [ptws_krawczyk_fderiv_matrix_comp]
  -- apply ContinuousLinearMap.nnnorm_def
  generalize hM : (1 - (jacobianEvalWithPrec prec S V).ApproxInverse * S.exactJacobian v) = M
  simp only [ptws_krawczyk_fderiv_matrix_comp, hM, Matrix.toLin'_apply']
  apply ContinuousLinearMap.opNorm_le_bound
  · simp only [NNReal.val_eq_coe, NNReal.zero_le_coe]
  · simp only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecBilin_apply, NNReal.val_eq_coe]
    intro x; unfold Matrix.mulVec
    simp only [_root_.dotProduct]
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (NNReal.zero_le_coe) (_root_.norm_nonneg _))]
    intro i; apply le_trans (norm_sum_le _ _)
    simp only [norm_mul]
    have h₁ : ∑ x_1, ‖M i x_1‖ * ‖x x_1‖ ≤ (∑ x_1, ‖M i x_1‖) * ‖x‖ := by
      rw [Finset.sum_mul]
      gcongr; apply norm_le_pi_norm
    apply le_trans h₁; gcongr
    simp only [contractionFactor']
    apply Matrival.mem_abs_le
    rw [← hM]
    apply sub_sound (one_mem)
    apply Matrival.mul_sound (approx_inverse_mem prec _) (exact_jacobian_sound prec S V _ hv)

variable (Y : Matrix (Fin n) (Fin m) ℝ) (V : Vecterval n)

def lipschitzOnWith := Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (ptws_krawczyk_fderiv S (jacobianEvalWithPrec prec S V).ApproxInverse V) (ptws_krawczyk_deriv_norm_le prec S V) V.convex

def restrict_lipschitzWith :=
  LipschitzOnWith.to_restrict (lipschitzOnWith prec S V)

instance KrawczykContraction {V : Vecterval n} (h₁ : Krawczyk prec S V ⊆ V)(h₂ :  contractionFactor' prec S V < 1) :
  ContractingWith (contractionFactor' prec S V)
  (Set.MapsTo.restrict (ptwsKrawczyk S (jacobianEvalWithPrec prec S V).ApproxInverse)
    V.toSet V.toSet (ptws_krawczyk_mapsTo prec S V h₁)) where
  left := h₂
  right := restrict_lipschitzWith prec S V -- Get this using Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le


variable (h₁ : Krawczyk prec S V ⊆ V)(h₂ :  contractionFactor' prec S V < 1)

#check edist_ne_top
#check ContractingWith.exists_fixedPoint' (complete V) (ptws_krawczyk_mapsTo prec S V h₁) (KrawczykContraction prec S h₁ h₂)

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
