import Mathlib
import Krawcheck.DyadicIntervals
import Krawcheck.PolynomialBounds
import Krawcheck.PolynomialRoots
import Krawcheck.MvPolynomials

-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false
-- set_option pp.all true

/-!
# Krawczyk Method
This file contains the implementation and proofs of the Krawczyk method for root isolation
of systems of multivariate polynomials.

## Main Definitions
- `Krawczyk`: The Krawczyk operator that maps a `Vecterval` to another `Vecterval` based on the system `S` and a
  preconditioner matrix `Y`.
- `ptwsKrawczyk`: The pointwise Krawczyk map from `ℝ^n` to `ℝ^n` that corresponds to the `Krawczyk` operator on `Vecterval`.
- `ptwsKrawczykFDeriv`: The Fréchet derivative of the pointwise Krawczyk map.
- `contractionFactor`: Contraction factor of the Krawczyk operator on a `Vecterval`, i.e. `‖I - Y * JX‖`.
- `IsolateRoots` : A function that returns two lists of `Vecterval` within the input `Vecterval`. The first list
  contains `Vecterval`s that are certified to each have a unique root of the system, and the second list contains
  `Vecterval`s that might have a root of the system.

## Main Theorems
- `krawczyk_sound`: Image of the `Krawczyk` operator contains the image of `ptwsKrawczyk` on any `Vecterval`
- `ptws_krawczyk_deriv_norm_le` : The norm of the Fréchet derivative of the pointwise Krawczyk map is
  bounded by the contraction factor.
- `krawczyk_fixedPoint`: Banach Fixed Point theorem applied to `ptwsKrawczyk`
-/

namespace Vecterval
section VectervalAddendum
open Set MvRatPol Vecterval System
variable {m n : ℕ} (prec : ℤ)(p : MvRatPol n) (S : System m n) (X Y : Vecterval n)

def HasRoot' := ∃ x ∈ X, (toMvRealPoly p).eval x.get = 0
def HasUniqueRoot' := ∃! x ∈ X, (toMvRealPoly p).eval x.get = 0
def HasNoRoot' := ∀ x ∈ X, (toMvRealPoly p).eval x.get ≠ 0

def HasRoot := ∃ x ∈ X, S.eval' x.get = 0
def HasUniqueRoot := ∃! x ∈ X, S.eval' x.get = 0
def HasNoRoot := ∀ x ∈ X, S.eval' x.get ≠ 0

theorem hasNoRoot_iff_not_hasRoot : X.HasNoRoot S ↔ ¬ X.HasRoot S := by grind only [HasRoot, HasNoRoot]

theorem hasRoot_of_hasUniqueRoot (h : X.HasUniqueRoot S) : X.HasRoot S := by
  simp only [HasUniqueRoot, HasRoot] at *
  apply ExistsUnique.exists; exact h

theorem has_no_root_subset (h : X ⊆ Y) (h': Y.HasNoRoot S) : X.HasNoRoot S := by
  intro x hx; apply h'
  grind only [mem_iff_get_mem_toSet, mem_of_subset_of_mem, subset_iff_toSet]

theorem subset_has_root (h : X ⊆ Y) (h' : X.HasRoot S) : Y.HasRoot S := by
  simp only [HasRoot] at *
  obtain ⟨x, hx, hx'⟩ := h'
  use x; grind only [mem_iff_get_mem_toSet, mem_of_subset_of_mem, subset_iff_toSet]

#check System.vecterval_eval_sound
theorem no_root_of_eval_zerofree (h : ZeroFree (S.vectervalEvalWithPrec prec X)) : X.HasNoRoot S := by
  intro x hx
  by_contra h₀
  rw [← eval_eq] at h₀
  have : S.eval x = 0 := by
    ext i hi; replace h₀ := congr_fun h₀
    simp only [Vector.get_eq_getElem, Pi.zero_apply] at h₀
    rw [h₀ ⟨i, hi⟩]; simp only [Vector.getElem_zero]
  have : 0 ∈ (System.vectervalEvalWithPrec prec S X) := by
    grind only [System.vecterval_eval_sound]
  grind only [zerofree_iff_not_mem_zero]

theorem haszero_of_eval (h : X.HasRoot S) : HasZero (S.vectervalEvalWithPrec prec X) := by
  obtain ⟨x, hx, hx'⟩ := h
  rw [haszero_iff_mem_zero]
  rw [← eval_eq] at hx'
  have : S.eval x = 0 := by
    ext i hi; replace h₀ := congr_fun hx'
    simp only [Vector.get_eq_getElem, Pi.zero_apply] at h₀
    rw [h₀ ⟨i, hi⟩]; simp only [Vector.getElem_zero]
  grind only [System.vecterval_eval_sound]

end VectervalAddendum
end Vecterval

namespace Vecterval
section KrawczykProofs
open Dyadic DyadicInterval Vecterval Matrival MvRatPol System
variable (prec : ℤ) {m n : ℕ} (S : System m n)
variable (Y : Matrix (Fin n) (Fin m) ℚ)

-- If required, pass Y as an argument for later convenience
def Krawczyk (V : Vecterval n) : Vecterval n :=
  let Vm : Vecterval n := V.midpoint
  let fVm := S.evalWithPrec prec V.midpoint_rat
  let JX := jacobianEvalWithPrec prec S V
  let Y := Matrival.ofRatWithPrec prec Y --ApproxInvWithPrec prec JX
  Vm - Y * fVm + (Matrival.one - Y * JX) * (V - Vm)
  -- V - Y * (fVm + JX * (V - (V.midpoint : Vecterval n)))
  -- This has to be in the original form! Otherwise it might not contract!!
  -- The whole point of I - Y* J is the contraction...
  -- What we have now, contains the original due to subdistributivity, but recall we don't have distributivity!

def contractionFactor (V : Vecterval n) : Dyadic :=
  let JX := jacobianEvalWithPrec prec S V
  let Y := Matrival.ofRatWithPrec prec Y--ApproxInvWithPrec prec JX
  let I := @Matrival.one n
  (I - Y * JX).norm

def contractionFactor' (V : Vecterval n) : NNReal :=
  let JX := jacobianEvalWithPrec prec S V
  let Y := Matrival.ofRatWithPrec prec Y --ApproxInvWithPrec prec JX
  let I := @Matrival.one n
  (I - Y * JX).norm'

-- def isContraction  (V : Vecterval n) : Prop := contractionFactor' prec S V < 1
noncomputable def ptwsKrawczyk (v : Fin n → ℝ) : Fin n → ℝ :=
  v - (Y.map Rat.cast).mulVec (S.eval' v)
  -- m - (Y.map Rat.cast).mulVec (S.eval' m) + (1 - (Y.map Rat.cast) * J c).mulVec (v - m)
  -- There need to be two froms for this...

variable (f : Fin n → ℝ)
theorem ptwsKrawczyk_mvt (V : Vecterval n) :  ∀ v ∈ V, ∃ ξ,
  (∀ i, Vector.ofFn (ξ i) ∈ V) ∧ (ptwsKrawczyk S Y v.get) =
  (V.midpoint_real).get - (Y.map Rat.cast).mulVecᵣ (S.eval' (V.midpoint_real).get)
  + ((1 : Matrix (Fin n) (Fin n) ℝ) -  Y.map Rat.cast * (mixedJacobian S ξ)).mulVecᵣ
  (v.get - V.midpoint_real.get) := by
  unfold ptwsKrawczyk; intro v hv
  obtain ⟨ξ, h⟩ := mvt_real_sys' S V v hv; use ξ
  have : v.get = V.midpoint_real.get + Matrix.mulVec 1 (v.get - V.midpoint_real.get) := by
    grind only [Matrix.one_mulVec]
  nth_rw 1 [this]
  rw [h.2, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_sub_add_comm, ← Matrix.sub_mulVec]
  simp only [Matrix.mulVecᵣ_eq, and_true]
  exact h.1

theorem krawczyk_sound (S : System m n) (V : Vecterval n) : ∀ v ∈ V,
  (ptwsKrawczyk S Y v.get) ∈ (Krawczyk prec S Y V).toSet := by
  -- generalize h : (Y.map Rat.cast) = Y
  intro v hv
  obtain ⟨ξ, h₁, h₂⟩ := ptwsKrawczyk_mvt S Y V v hv
  -- rw [h, Krawczyk]
  rw [Vecterval.mem_toSet_iff, h₂, Krawczyk]
  simp only [mem_iff, get_add, get_sub, Pi.add_apply, Pi.sub_apply, Vector.get_ofFn]
  intro i
  apply DyadicInterval.add_sound
  · apply DyadicInterval.sub_sound
    · simp only [ofVecDyadic, midpoint, Vector.map_map, Vector.get_map, Function.comp_apply,
      midpoint_real, midpoint_rat]
      apply to_rat_mem_of_dyadic
    · rw [← Vector.get_ofFn ((Y.map Rat.cast).mulVecᵣ (S.eval' V.midpoint_real.get))]
      apply (mem_iff _ _).mp
      rw [← eval_eq]
      apply mulVec_sound
      · apply real_mem_matrival
      · simp only [midpoint_real]
        apply System.eval_sound
  · rw [← Vector.get_sub v V.midpoint_real]
    generalize h' : ((1 : Matrix (Fin n) (Fin n) ℝ) - Y.map Rat.cast * mixedJacobian S ξ).mulVecᵣ (v - V.midpoint_real).get = f
    rw [← Vector.get_ofFn f]
    apply (mem_iff _ _).mp
    rw [← h']
    apply mulVec_sound
    · apply Matrival.sub_sound Matrival.one_mem
      apply Matrival.mul_sound (Matrival.real_mem_matrival prec _)
      apply mixedJacobian_sound prec S V ξ h₁

    · apply Vecterval.sub_sound _ _ _ _ hv
      simp only [ofVecDyadic, midpoint, Vector.map_map, midpoint_real, midpoint_rat, mem_iff,
        Vector.get_map, Function.comp_apply]; intro k
      apply to_rat_mem_of_dyadic

noncomputable def ptwsKrawczykFDeriv
  (f : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
  ContinuousLinearMap.id ℝ (Fin n → ℝ) - (LinearMap.toContinuousLinearMap (Matrix.toLin' (Y.map Rat.cast))).comp
      (ContinuousLinearMap.pi (fun i ↦ (S.get i).fderiv f))

theorem ptws_krawczyk_fderiv_matrix_comp (S : System m n)
  (f : Fin n → ℝ) : ptwsKrawczykFDeriv S Y f = LinearMap.toContinuousLinearMap
  ((1 - (Y.map (@Rat.cast ℝ _)) * (exactJacobian S f))).toLin' := by
  simp only [ptwsKrawczykFDeriv, map_sub, Matrix.toLin'_one, Matrix.toLin'_mul]
  have : ContinuousLinearMap.id ℝ (Fin n → ℝ) = LinearMap.toContinuousLinearMap LinearMap.id := by rfl
  simp only [this, sub_right_inj]
  change (LinearMap.toContinuousLinearMap (Matrix.toLin' (Y.map Rat.cast))).comp (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv f) =
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Y.map Rat.cast) ∘ₗ Matrix.toLin' (LinearMap.toMatrix' (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv f).toLinearMap))
  simp only [Matrix.toLin'_toMatrix']; congr

theorem ptws_krawczyk_fderiv (S : System m n)
  (V : Vecterval n) : ∀ v ∈ V.toSet, HasFDerivWithinAt
  (ptwsKrawczyk S Y) (ptwsKrawczykFDeriv S Y v) V.toSet v := by
  intro v hv
  unfold ptwsKrawczyk ptwsKrawczykFDeriv
  apply HasFDerivWithinAt.sub
  · simp only [hasFDerivWithinAt_pi', ContinuousLinearMap.comp_id]
    intro i; apply hasFDerivWithinAt_apply
  · simp only [hasFDerivWithinAt_pi']; intro i
    -- Rewrite Y * f(x) i as some f ∘ g
    change HasFDerivWithinAt ((fun y ↦ y i) ∘ (fun x ↦ (Y.map Rat.cast).mulVec (S.eval' x))) ((ContinuousLinearMap.proj i).comp
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' (Y.map Rat.cast))).comp
      (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv v))) V.toSet v
    apply HasFDerivWithinAt.comp v (hasFDerivWithinAt_apply _ _ _) _ (Set.mapsTo_univ _ _)
    -- Rewrite Y * f(x) as some f ∘ g
    change HasFDerivWithinAt ((fun y ↦ (Y.map Rat.cast).mulVec y) ∘ (fun x ↦ S.eval' x)) ((LinearMap.toContinuousLinearMap (Matrix.toLin' (Y.map Rat.cast))).comp (ContinuousLinearMap.pi fun i ↦ (Vector.get S i).fderiv v)) V.toSet v
    apply HasFDerivWithinAt.comp v _ _ (Set.mapsTo_univ _ _)
    · -- Rewrite (fun y ↦ Y.mulVec y) as a CtsLinMap
      change HasFDerivWithinAt ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' (Y.map Rat.cast))) (LinearMap.toContinuousLinearMap (Matrix.toLin' (Y.map Rat.cast))) Set.univ (S.eval' v)
      apply ContinuousLinearMap.hasFDerivWithinAt
    · grind only [hasFDerivWithinAt_pi', ContinuousLinearMap.proj_pi, eval', hasFDerivWithinAt_eval]

theorem ptws_krawczyk_mapsTo (S : System m n) (V : Vecterval n) (hK : Krawczyk prec S Y V ⊆ V):
  Set.MapsTo (ptwsKrawczyk S (Y.map Rat.cast)) V.toSet V.toSet := by
  simp only [Set.mapsTo_iff_image_subset, Set.image_subset_iff]
  intro v hv; simp only [Set.mem_preimage]
  rw [mem_toSet_iff] at hv
  rw [Vector.get_ofFn' v]
  apply Set.mem_of_mem_of_subset
  · exact (krawczyk_sound prec Y S V _ hv)
  · grind only [= subset_iff_toSet]

theorem ptws_krawczyk_deriv_norm_le (S : System m n) (V : Vecterval n) : ∀ v ∈ V.toSet,
  ‖ptwsKrawczykFDeriv S Y v‖₊ ≤ contractionFactor' prec S Y V := by
  intro v hv
  generalize hM : (1 - (Y.map (@Rat.cast ℝ _)) * S.exactJacobian v) = M
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
    apply Matrival.sub_sound (one_mem)
    exact Matrival.mul_sound (real_mem_matrival prec Y) (exact_jacobian_sound prec S V _ hv)

instance KrawczykContraction {V : Vecterval n} (h₁ : Krawczyk prec S Y V ⊆ V)
  (h₂ :  contractionFactor' prec S Y V < 1) :
  ContractingWith (contractionFactor' prec S Y V)
  (Set.MapsTo.restrict (ptwsKrawczyk S (Y.map Rat.cast))
    V.toSet V.toSet (ptws_krawczyk_mapsTo prec Y S V h₁)) where
  left := h₂
  right := LipschitzOnWith.to_restrict (Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (ptws_krawczyk_fderiv Y S V) (ptws_krawczyk_deriv_norm_le prec Y S V) V.convex)

lemma edist_ne_top (V : Vecterval n) : ∀ v ∈ V.toSet, edist v
  (ptwsKrawczyk S (Y.map Rat.cast) v) ≠ ⊤ := by
  intro v hv; apply _root_.edist_ne_top

/-- If the Krawczyk map is contractive and maps the `Vecterval` into itself,
then there is a fixed point of the pointwise Krawczyk map in the `Vecterval` -/
theorem krawczyk_fixedPoint {S : System m n} {V : Vecterval n} (hsub : Krawczyk prec S Y V ⊆ V)
  (hlt : contractionFactor' prec S Y V < 1) : ∃ y ∈ V, Function.IsFixedPt (ptwsKrawczyk S Y) y.get := by
  have hv_mid := ((mem_iff_get_mem_toSet V V.midpoint_real).mp V.midpoint_mem)
  obtain ⟨y, hy, hy', _ ⟩ := ContractingWith.exists_fixedPoint' (complete V) (ptws_krawczyk_mapsTo prec Y S V hsub) (KrawczykContraction prec S Y hsub hlt) hv_mid (edist_ne_top S Y V _ hv_mid)
  rw [mem_toSet_iff] at hy
  rw [Vector.get_ofFn' y] at hy'
  use Vector.ofFn y, hy, hy'

lemma krawczyk_restriction_fixedPoint {S : System m n} {V : Vecterval n} (hsub : Krawczyk prec S Y V ⊆ V)
  (hlt : contractionFactor' prec S Y V < 1) : ∃ (y : Fin n → ℝ) (hy : y ∈ V.toSet), Function.IsFixedPt (Set.MapsTo.restrict
  (ptwsKrawczyk S (Y.map Rat.cast)) V.toSet V.toSet ((ptws_krawczyk_mapsTo prec Y S V hsub))) ⟨y, hy⟩ := by
  obtain ⟨y, hy, hy'⟩ := krawczyk_fixedPoint prec Y hsub hlt
  rw [mem_iff_get_mem_toSet] at hy
  use y.get, hy
  exact Subtype.ext hy'

/-- If the Krawczyk map is contractive and maps the `Vecterval` into itself, then there
is a unique fixed point of the pointwise Krawczyk map in the `Vecterval` -/
theorem krawczyk_unique_fixedPoint {S : System m n} {V : Vecterval n} (hsub : Krawczyk prec S Y V ⊆ V)
  (hlt : contractionFactor' prec S Y V < 1) : ∃! y ∈ V, Function.IsFixedPt (ptwsKrawczyk S Y) y.get := by
  apply existsUnique_of_exists_of_unique
  · exact krawczyk_fixedPoint prec Y hsub hlt
  · intro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    rw [mem_iff_get_mem_toSet] at hx hy
    replace hx' :  Function.IsFixedPt (Set.MapsTo.restrict (ptwsKrawczyk S Y) V.toSet V.toSet
      ((ptws_krawczyk_mapsTo prec Y S V hsub))) ⟨x.get, hx⟩ := by exact Subtype.ext hx'
    replace hy' : Function.IsFixedPt (Set.MapsTo.restrict (ptwsKrawczyk S Y) V.toSet V.toSet
      ((ptws_krawczyk_mapsTo prec Y S V hsub))) ⟨y.get, hy⟩ := by exact Subtype.ext hy'
    have h := ContractingWith.fixedPoint_unique' (KrawczykContraction prec S Y hsub hlt) hx' hy'
    simp only [Subtype.mk.injEq] at h
    replace h := congr_fun h
    simp only [Vector.get_eq_getElem] at h
    ext i hi
    exact h ⟨i, hi⟩

/-- If a root is in the `Vecterval`, then it must be in the Krawczyk image of the `Vecterval` -/
theorem has_root_of_krawczyk_has_root {S : System m n} {V : Vecterval n}
  {v : Vector ℝ n} (hv : v ∈ V) : S.eval' v.get = 0 → v ∈ (Krawczyk prec S Y V) := by
  intro hz
  have : (ptwsKrawczyk S Y) v.get = v.get := by
    simp only [ptwsKrawczyk, hz, Matrix.mulVec_zero,
    sub_zero]
  rw [mem_iff_get_mem_toSet, ← this]
  exact krawczyk_sound prec Y S V v hv

/-- If the `Vecterval` and its Krawczyk image are disjoint, then there is no root in the `Vecterval` -/
theorem krawczyk_disjoint_of_has_no_root {S : System m n} {V : Vecterval n}
  (h : V ⊓ (Krawczyk prec S Y V) = none) : V.HasNoRoot S := by
  by_contra hf; rw [hasNoRoot_iff_not_hasRoot, not_not] at hf
  obtain ⟨x, hx, hx'⟩ := hf
  have hx'' := has_root_of_krawczyk_has_root prec Y hx hx'
  have h' := inter_toSet_none _ _ h; rw [← Set.disjoint_iff_inter_eq_empty] at h'
  have : ¬Disjoint V.toSet (Krawczyk prec S Y V).toSet := by
    grind only [Set.not_disjoint_iff_nonempty_inter, Set.inter_nonempty, mem_iff_get_mem_toSet]
  grind only

end KrawczykProofs

section KrawczykMethod
open Vecterval Matrival MvRatPol System
variable {m n : ℕ} (prec : ℤ) (S : System (n+1) (n+1))
  (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V : Vecterval (n + 1))

/-- If the Krawczyk map is contractive and maps the `Vecterval` into itself, then a
fixed point of the pointwise Krawczyk map is a root of the `System` and vice versa -/
theorem fixed_pt_iff_root (hsub : Krawczyk prec S Y V ⊆ V)
  (hlt : contractionFactor' prec S Y V < 1) (hdet : Y.det ≠ (0 : ℚ)) : ∀ y,
  Function.IsFixedPt (ptwsKrawczyk S Y) y ↔ S.eval' y = 0 := by
  intro y; constructor <;> intro h
  · replace h := Function.IsFixedPt.eq h
    simp only [ptwsKrawczyk, sub_eq_self] at h
    apply Matrix.eq_zero_of_mulVec_eq_zero _ h
    change ((algebraMap ℚ ℝ).mapMatrix Y).det ≠ 0
    rw [← RingHom.map_det (algebraMap ℚ ℝ)]
    simp only [eq_ratCast, ne_eq, Rat.cast_eq_zero, hdet, not_false_eq_true]
  · rw [← Function.mem_fixedPoints, Function.mem_fixedPoints_iff]
    simp only [ptwsKrawczyk, h, Matrix.mulVec_zero, sub_zero]

/-- If the Krawczyk map is contractive and maps the `Vecterval` into itself, then there is
a root of the `System` in the `Vecterval` -/
theorem krawczyk_root (hsub : Krawczyk prec S Y V ⊆ V)
  (hlt : contractionFactor' prec S Y V < 1) (hdet : Y.det ≠ (0 : ℚ)) :
  ∃ y ∈ V, (S.eval' y.get) = 0 := by
  obtain ⟨y, hy, hy'⟩ := krawczyk_fixedPoint prec Y hsub hlt
  rw [fixed_pt_iff_root prec S Y V hsub hlt hdet] at hy'
  use y, hy, hy'

/-- If the Krawczyk map is contractive and maps the `Vecterval` into itself, then
there is a unique root of the `System` in the `Vecterval` -/
theorem krawczyk_unique_root (hsub : Krawczyk prec S Y V ⊆ V)
  (hlt : contractionFactor' prec S Y V < 1) (hdet : Y.det ≠ (0 : ℚ)) :
  ∃! y ∈ V, (S.eval' y.get) = 0 := by
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := krawczyk_unique_fixedPoint prec Y hsub hlt
  apply existsUnique_of_exists_of_unique
  · exact krawczyk_root prec S Y V hsub hlt hdet
  · intro u v hu hv
    rw [←fixed_pt_iff_root prec S Y V hsub hlt hdet] at hu hv
    rw [(hy₃ u hu), (hy₃ v hv)]


/-- Jacobian of system evaluated on the interval is non-singular and Krawczyk map is contractive -/
def isValidKrawczyk :=
  let J := jacobianEvalWithPrec prec S V
  let J' := J.rat_midpoint
  let I := @Matrival.one (n + 1)
  (Y.det ≠ (0 : ℚ)) ∧ Matrival.norm (I - (Matrival.ofRatWithPrec prec Y) * J) < 1

instance : Decidable (isValidKrawczyk prec S Y V) := by
  simp only [isValidKrawczyk]; infer_instance

def IsolateRoots (prec : ℤ) (S : System (n+1) (n+1))
  (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V : Vecterval (n + 1))
  (max_depth : ℕ) (min_width: Dyadic := 0) : List (Vecterval (n + 1)) × List (Vecterval (n + 1)) :=
  if (S.vectervalEvalWithPrec prec V).ZeroFree then ([], [])
    else if isValidKrawczyk prec S (Y V) V then
      let K := V.Krawczyk prec S (Y V)
      match V ⊓ K with
      | none => ([], [])
      | some Z => if K ⊆ V then ([V], [])
          else if (Z.maxWidth ≤ min_width) ∨ (max_depth = 0) then ([],[V])
          --else IsolateRoots prec S Y Z (max_depth - 1) (min_width)
          else let (L, R) := V.split_along (V.maxWidthIdx)
          let rL := IsolateRoots prec S Y L (max_depth - 1) (min_width)
          let rR := IsolateRoots prec S Y R (max_depth - 1) (min_width)
          (rL.1 ++ rR.1, rL.2 ++ rR.2)
    else if max_depth = 0 then ([],[V])
    else let (L, R) := V.split_along (V.maxWidthIdx)
    let rL := IsolateRoots prec S Y L (max_depth - 1) (min_width)
    let rR := IsolateRoots prec S Y R (max_depth - 1) (min_width)
    (rL.1 ++ rR.1, rL.2 ++ rR.2)

/-- If `IsolateRoots` returns both lists empty then the `Vecterval` has no root of the `System` -/
theorem isolate_roots_empty_of_has_no_roots {n : ℕ} (prec : ℤ) (S : System (n+1) (n+1))
  (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V : Vecterval (n + 1))
  (max_depth : ℕ) (min_width : Dyadic) :
  IsolateRoots prec S Y V max_depth min_width = ([], []) → V.HasNoRoot S := by
  intro h; rw [IsolateRoots] at h
  split_ifs at h with hzf hvalid hmax
  · grind only [no_root_of_eval_zerofree]
  · simp only at h; split at h
    · rename_i heq
      apply krawczyk_disjoint_of_has_no_root _ _ heq
    · split_ifs at h
      · exfalso; grind only
      · exfalso; grind only
      · simp only [Prod.mk.injEq, List.append_eq_nil_iff] at h
        have h₁ : (IsolateRoots prec S Y (V.split_along V.maxWidthIdx).1
          (max_depth - 1) min_width) = ([], []) := by grind only
        have h₂ : (IsolateRoots prec S Y (V.split_along V.maxWidthIdx).2
          (max_depth - 1) min_width) = ([], []) := by grind only
        have h₁ : (V.split_along V.maxWidthIdx).1.HasNoRoot S := by
          apply isolate_roots_empty_of_has_no_roots; exact h₁
        have h₂ : (V.split_along V.maxWidthIdx).2.HasNoRoot S := by
          apply isolate_roots_empty_of_has_no_roots; exact h₂
        unfold HasNoRoot at *; intro x hx
        grind only [mem_split]

  · grind only
  · simp only [Prod.mk.injEq, List.append_eq_nil_iff] at h
    have h₁ : (IsolateRoots prec S Y (V.split_along V.maxWidthIdx).1
      (max_depth - 1) min_width) = ([], []) := by grind only
    have h₂ : (IsolateRoots prec S Y (V.split_along V.maxWidthIdx).2
      (max_depth - 1) min_width) = ([], []) := by grind only
    have h₁ : (V.split_along V.maxWidthIdx).1.HasNoRoot S := by
      apply isolate_roots_empty_of_has_no_roots; exact h₁
    have h₂ : (V.split_along V.maxWidthIdx).2.HasNoRoot S := by
      apply isolate_roots_empty_of_has_no_roots; exact h₂
    unfold HasNoRoot at *; intro x hx
    grind only [mem_split]

lemma lt_norm_iff_lt_norm' (A : Matrival m n) (a : Dyadic) (ha : (0 : ℝ) < a.toRat) :
  A.norm < a ↔ A.norm' < ⟨a.toRat, (LT.lt.le ha)⟩ := by
  simp only [Matrival.norm, Finset.fold_max_lt, Finset.mem_univ, forall_const, Matrival.norm']
  constructor <;> intro h
  · rw [Finset.sup_lt_iff (by norm_cast)]
    simp only [Finset.mem_univ, forall_const]
    intro j; unfold norm'; rw [Subtype.mk_lt_mk]
    grind only [Rat.cast_lt, Dyadic.toRat_lt_toRat_iff]

  · rw [Finset.sup_lt_iff (by norm_cast)] at h
    simp only [Finset.mem_univ, forall_const] at h
    norm_cast at ha; rw [← Dyadic.toRat_zero, Dyadic.toRat_lt_toRat_iff] at ha
    simp only [ha, true_and]; intro i
    specialize h i; rw [norm', Subtype.mk_lt_mk, Rat.cast_lt, Dyadic.toRat_lt_toRat_iff] at h
    exact h

/-- If `IsolateRoots` returns `Vecterval`s in the first list and nothing in the second list,
then each of these `Vecterval`s has a unique root of the `System` -/
theorem isolate_roots_of_has_unique_root {n : ℕ} (prec : ℤ) (S : System (n+1) (n+1))
  (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V : Vecterval (n + 1))
  (max_depth : ℕ) (min_width : Dyadic) :
  ∀ X ∈ (IsolateRoots prec S Y V max_depth min_width).1, X.HasUniqueRoot S := by
  induction max_depth generalizing V with
  | zero =>
    unfold IsolateRoots; split_ifs with hzf
    · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    · rename_i hv; obtain ⟨hdet, hlt⟩ := hv
      simp only; split
      · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
      · split_ifs with hsub h
        · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
          rw [lt_norm_iff_lt_norm' _ _ (by norm_cast)] at hlt
          simp only [Dyadic.toRat_one, Rat.cast_one, NNReal.mk_one] at hlt
          have hlt' : contractionFactor' prec S (Y V) V < 1 := by simp only [contractionFactor', hlt]
          simp only [HasUniqueRoot]
          exact krawczyk_unique_root prec S (Y V) V hsub hlt' hdet
        · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
        · grind only
    · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    · grind only

  | succ d ih =>
    unfold IsolateRoots; split_ifs with hzf hvalid
    · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    · obtain ⟨hdet, hlt⟩ := hvalid
      simp only [or_false, add_tsub_cancel_right]
      split
      · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
      · split_ifs with hsub h
        · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
          rw [lt_norm_iff_lt_norm' _ _ (by norm_cast)] at hlt
          simp only [Dyadic.toRat_one, Rat.cast_one, NNReal.mk_one] at hlt
          have hlt' : contractionFactor' prec S (Y V) V < 1 := by simp only [contractionFactor', hlt]
          simp only [HasUniqueRoot]
          exact krawczyk_unique_root prec S (Y V) V hsub hlt' hdet
        · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
        · grind only [List.mem_append]
    · grind only
    · grind only [add_tsub_cancel_right, List.mem_append]

lemma isolate_roots_subset {n : ℕ} (prec : ℤ) (S : System (n+1) (n+1))
  (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V X : Vecterval (n + 1))
  (max_depth : ℕ) (min_width : Dyadic) : X ∈ (IsolateRoots prec S Y V max_depth min_width).1 ∨
  X ∈ (IsolateRoots prec S Y V max_depth min_width).2 → X ⊆ V := by
  induction max_depth generalizing V with
  | zero =>
    simp only [IsolateRoots, or_true, ↓reduceIte]
    split
    · grind only [← List.not_mem_nil]
    · split_ifs with h₁ h₂
      · split
        · grind only [→ inter_subset]
        · grind only [= subset_iff, = List.mem_cons, ← List.not_mem_nil,
          DyadicInterval.subset_refl]
      · split
        · grind only [← List.not_mem_nil]
        · grind only [= subset_iff, ← List.not_mem_nil, = List.mem_cons,
          DyadicInterval.subset_refl]
      · grind only [← List.not_mem_nil, = List.mem_cons, = subset_iff, DyadicInterval.subset_refl]

  | succ d ih =>
    rw [IsolateRoots]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    split
    · grind only [← List.not_mem_nil]
    · split_ifs with h₁ h₂
      · split
        · grind only [→ inter_subset]
        · grind only [= subset_iff, = List.mem_cons, ← List.not_mem_nil,
          DyadicInterval.subset_refl]
      · split
        · grind only [← List.not_mem_nil]
        · split_ifs with heq
          · grind only [= subset_iff, ← List.not_mem_nil, = List.mem_cons,
            DyadicInterval.subset_refl]
          · simp only [add_tsub_cancel_right, List.mem_append]
            rintro ((h | h) | (h | h))
            · replace h := ih (V.split_along V.maxWidthIdx).1 (Or.inl h)
              have h' := left_split_subset V V.maxWidthIdx
              simp only [subset_iff_toSet] at *
              exact subset_trans h h'
            · replace h := ih (V.split_along V.maxWidthIdx).2 (Or.inl h)
              have h' := right_split_subset V V.maxWidthIdx
              simp only [subset_iff_toSet] at *
              exact subset_trans h h'
            · replace h := ih (V.split_along V.maxWidthIdx).1 (Or.inr h)
              have h' := left_split_subset V V.maxWidthIdx
              simp only [subset_iff_toSet] at *
              exact subset_trans h h'
            · replace h := ih (V.split_along V.maxWidthIdx).2 (Or.inr h)
              have h' := right_split_subset V V.maxWidthIdx
              simp only [subset_iff_toSet] at *
              exact subset_trans h h'
      · simp only [add_tsub_cancel_right, List.mem_append]
        rintro ((h | h) | (h | h))
        · replace h := ih (V.split_along V.maxWidthIdx).1 (Or.inl h)
          have h' := left_split_subset V V.maxWidthIdx
          simp only [subset_iff_toSet] at *
          exact subset_trans h h'
        · replace h := ih (V.split_along V.maxWidthIdx).2 (Or.inl h)
          have h' := right_split_subset V V.maxWidthIdx
          simp only [subset_iff_toSet] at *
          exact subset_trans h h'
        · replace h := ih (V.split_along V.maxWidthIdx).1 (Or.inr h)
          have h' := left_split_subset V V.maxWidthIdx
          simp only [subset_iff_toSet] at *
          exact subset_trans h h'
        · replace h := ih (V.split_along V.maxWidthIdx).2 (Or.inr h)
          have h' := right_split_subset V V.maxWidthIdx
          simp only [subset_iff_toSet] at *
          exact subset_trans h h'

-- theorem isolate_roots_of_has_root {n : ℕ} (prec : ℤ) (S : System (n+1) (n+1))
--   (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V X : Vecterval (n + 1))
--   (Xs Ys : List (Vecterval (n+1))) (max_depth : ℕ) (min_width : Dyadic) :
--   IsolateRoots prec S Y V max_depth min_width = (X :: Xs, Ys) → V.HasRoot S := by
--   intro h
--   have h' := isolate_roots_of_has_unique_root prec S Y V max_depth min_width X
--   simp only [h, List.mem_cons, true_or, forall_const] at h'
--   replace h' := hasRoot_of_hasUniqueRoot _ _ h'
--   apply subset_has_root _ _ _ _ h'
--   apply isolate_roots_subset prec S Y V X max_depth min_width
--   left; simp only [h, List.mem_cons, true_or]

/-- If `IsolateRoots` returns a non-empty first list then the input `Vecterval` has a root of the `System` -/
theorem isolate_roots_of_has_root {n : ℕ} (prec : ℤ) (S : System (n+1) (n+1))
  (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V : Vecterval (n + 1)) (max_depth : ℕ)
  (min_width : Dyadic) : 0 < (IsolateRoots prec S Y V max_depth min_width).1.length → V.HasRoot S := by
  intro h; rw [List.length_pos_iff_exists_cons] at h
  obtain ⟨X, Xs, hX⟩ := h
  have h' := isolate_roots_of_has_unique_root prec S Y V max_depth min_width X
  simp only [hX, List.mem_cons, true_or, forall_const] at h'
  replace h' := hasRoot_of_hasUniqueRoot _ _ h'
  apply subset_has_root _ _ _ _ h'
  apply isolate_roots_subset prec S Y V X max_depth min_width
  left; simp only [hX, List.mem_cons, true_or]

/-- If the input `Vecterval` contains a root of the `System` it must be in
some `Vecterval` in the lists returned by `IsolateRoots` -/
theorem isolate_roots_sound {n : ℕ} (prec : ℤ) (S : System (n+1) (n+1))
  (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (V : Vecterval (n + 1))
  (max_depth : ℕ) (min_width : Dyadic) (v : Vector ℝ (n + 1)) (h_mem : v ∈ V)
  (h_root : S.eval' v.get = 0) : ∃ X, ((X ∈ (IsolateRoots prec S Y V max_depth min_width).1)
  ∨ (X ∈ (IsolateRoots prec S Y V max_depth min_width).2)) ∧ v ∈ X := by
  induction max_depth generalizing V with
  | zero =>
    simp only [IsolateRoots, or_true, ↓reduceIte]
    split_ifs with h₁ h₂ h₃
    · exfalso
      replace h₁ := mem_zerofree_neq_zero _ h₁
      rw [← eval_eq] at h_root
      have : S.eval v = 0 := by
        ext i hi; rw [← Vector.get_eq_getElem _ ⟨i,hi⟩]
        simp only [h_root, Pi.zero_apply, Vector.getElem_zero]
      replace h₁ := h₁ _ (System.vecterval_eval_sound prec S V v h_mem)
      grind only
    · split
      · exfalso
        rename_i heq
        replace heq := krawczyk_disjoint_of_has_no_root prec (Y V) heq
        grind only [HasNoRoot]
      · use V; simp only [List.mem_cons, List.not_mem_nil, or_false, true_and, h_mem]
    · split
      · exfalso
        rename_i heq
        replace heq := krawczyk_disjoint_of_has_no_root prec (Y V) heq
        grind only [HasNoRoot]
      · use V; simp only [List.not_mem_nil, List.mem_cons, or_false, or_true, h_mem, and_self]
    · use V; simp only [List.not_mem_nil, List.mem_cons, or_false, or_true, h_mem, and_self]

  | succ d ih =>
    rw [IsolateRoots]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false,
      or_false, add_tsub_cancel_right, ↓reduceIte]
    split_ifs with h₁ h₂ h₃
    · exfalso
      replace h₁ := mem_zerofree_neq_zero _ h₁
      rw [← eval_eq] at h_root
      have : S.eval v = 0 := by
        ext i hi; rw [← Vector.get_eq_getElem _ ⟨i,hi⟩]
        simp only [h_root, Pi.zero_apply, Vector.getElem_zero]
      replace h₁ := h₁ _ (System.vecterval_eval_sound prec S V v h_mem)
      grind only
    · split
      · exfalso
        rename_i heq
        replace heq := krawczyk_disjoint_of_has_no_root prec (Y V) heq
        grind only [HasNoRoot]
      · use V; simp only [List.not_mem_nil, List.mem_cons, or_false, h_mem, and_self]
    · split
      · exfalso
        rename_i heq
        replace heq := krawczyk_disjoint_of_has_no_root prec (Y V) heq
        grind only [HasNoRoot]
      · split_ifs
        · use V; simp only [List.not_mem_nil, List.mem_cons, or_false, or_true, h_mem, and_self]
        · simp only [List.mem_append]
          replace h_mem := mem_split V V.maxWidthIdx v h_mem
          grind only
    · simp only [List.mem_append]
      replace h_mem := mem_split V V.maxWidthIdx v h_mem
      grind only

-- theorem isolate_roots_of_unique_root' {n : ℕ} (prec : ℤ)
--   (S : System (n+1) (n+1)) (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
--   (V X : Vecterval (n + 1)) (max_depth : ℕ) (min_width : Dyadic) :
--   IsolateRoots prec S Y V max_depth min_width = ([X], []) → V.HasUniqueRoot S := by
--   intro h
--   apply existsUnique_of_exists_of_unique
--   · apply isolate_roots_of_has_root _ _ _ _ _ _ _ _ _ h
--   · have h' : X ∈ (IsolateRoots prec S Y V max_depth min_width).1 := by
--       simp only [h, List.mem_cons, List.not_mem_nil, or_false]
--     replace h' := isolate_roots_of_has_unique_root _ _ _ _ _ _ _ h'
--     obtain ⟨x, hx, hx'⟩ := h'
--     intro y₁ y₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
--     replace h₁ := isolate_roots_sound prec S Y V max_depth min_width _ h₁ h₁'
--     obtain ⟨X₁, hX₁⟩ := h₁
--     replace h₂ := isolate_roots_sound prec S Y V max_depth min_width _ h₂ h₂'
--     obtain ⟨X₂, hX₂⟩ := h₂
--     simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hX₁ hX₂
--     grind only

/-- If `IsolateRoots` returns ([X],[]), then the input `Vecterval` has a unique root of the `System` -/
theorem isolate_roots_of_unique_root' {n : ℕ} (prec : ℤ)
  (S : System (n+1) (n+1)) (Y : Vecterval (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
  (V : Vecterval (n + 1)) (max_depth : ℕ) (min_width : Dyadic) :
  (IsolateRoots prec S Y V max_depth min_width).1.length = 1 →
  (IsolateRoots prec S Y V max_depth min_width).2.length = 0 → V.HasUniqueRoot S := by
  intro h₁ h₂
  rw [List.length_eq_one_iff] at h₁; obtain ⟨X, h₁⟩ := h₁
  rw [List.length_eq_zero_iff] at h₂
  apply existsUnique_of_exists_of_unique
  · apply isolate_roots_of_has_root prec S Y V max_depth min_width
    simp only [h₁, List.length_cons, List.length_nil, zero_add, zero_lt_one]
  · have h' : X ∈ (IsolateRoots prec S Y V max_depth min_width).1 := by
      simp only [h₁, List.mem_cons, List.not_mem_nil, or_false]
    replace h' := isolate_roots_of_has_unique_root _ _ _ _ _ _ _ h'
    obtain ⟨x, hx, hx'⟩ := h'
    intro y₁ y₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    replace h₁ := isolate_roots_sound prec S Y V max_depth min_width _ h₁ h₁'
    obtain ⟨X₁, hX₁⟩ := h₁
    replace h₂ := isolate_roots_sound prec S Y V max_depth min_width _ h₂ h₂'
    obtain ⟨X₂, hX₂⟩ := h₂
    simp only [h₁, h₂, List.mem_cons, List.not_mem_nil, or_false] at hX₁ hX₂
    grind only

end KrawczykMethod
end Vecterval
