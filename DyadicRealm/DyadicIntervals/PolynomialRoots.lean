import Mathlib
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
import DyadicRealm.DyadicIntervals.Division
import DyadicRealm.DyadicIntervals.PolynomialBounds
-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace DyadicInterval
section PolynomialRoots
open Dyadic DyadicInterval Polynomial
variable (prec : ℤ) (I J: DyadicInterval) {n : ℕ} (p : RatPol n)

def HasRoot := ∃ x ∈ I, (toRealPoly p).eval x = 0

def HasNoRoot := ∀ x ∈ I, (toRealPoly p).eval x ≠ 0

def HasUniqueRoot := ∃! x ∈ I, (toRealPoly p).eval x = 0

theorem hasNoRoot_iff_not_hasRoot : I.HasNoRoot p ↔ ¬ (I.HasRoot p) := by
  simp only [HasNoRoot, HasRoot]
  simp only [mem_iff_mem_Icc, Set.mem_Icc, ne_eq, and_imp, not_exists, not_and]

theorem hasRoot_of_hasUniqueRoot (h : I.HasUniqueRoot p) : I.HasRoot p := by
  simp only [HasUniqueRoot, HasRoot] at *
  apply ExistsUnique.exists; exact h

theorem hasNoRoot_subset (h : J ⊆ I) (h_no : I.HasNoRoot p) :
  J.HasNoRoot p := by
  intro x hx; apply h_no
  exact Set.mem_of_subset_of_mem ((subset_iff J I).mp h) hx

theorem hasRoot_subset (h : J ⊆ I) (h_root : HasRoot J p) :
  I.HasRoot p := by
  simp only [HasRoot] at *
  obtain ⟨x, hx, hx'⟩ := h_root
  use x; constructor
  · exact (Set.mem_of_subset_of_mem ((subset_iff J I).mp h) hx)
  · exact hx'

theorem no_root_of_eval_zerofree (h : ZeroFree (intervalEvalWithPrec prec p I)) : I.HasNoRoot p := by
  unfold HasNoRoot
  intro x hx
  by_contra h₀
  have : 0 ∈ intervalEvalWithPrec prec p I := by rw [← h₀]; apply interval_eval_sound; exact hx
  rw [zerofree_iff_not_mem_zero] at h
  grind only

theorem haszero_of_eval (h : I.HasRoot p) : HasZero (intervalEvalWithPrec prec p I) := by
  unfold HasRoot at h
  obtain ⟨x, hx, hx'⟩ := h
  rw [haszero_iff_mem_zero, ← hx']
  apply interval_eval_sound; exact hx

abbrev StrictMonoOrStrictAnti := StrictAntiOn (toRealPoly p).eval I ∨ StrictMonoOn (toRealPoly p).eval I

lemma strict_mono_of_deriv_zerofree (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I)) :
   I.StrictMonoOrStrictAnti p:= by
  rw [zerofree_iff] at h
  rcases h with hneg | hpos
  · left
    apply strictAntiOn_of_deriv_neg (by apply convex_Icc) (by apply Polynomial.continuousOn)
    intro x hx
    simp only [Polynomial.deriv, ← deriv_eq_real_poly_deriv]
    apply neg_of_mem_neg _ hneg
    apply interval_eval_sound
    simp only [Membership.mem]
    apply Set.mem_of_subset_of_mem _ hx
    apply interior_subset

  · right
    apply strictMonoOn_of_deriv_pos (by apply convex_Icc) (by apply Polynomial.continuousOn)
    intro x hx
    simp only [Polynomial.deriv, ← deriv_eq_real_poly_deriv]
    apply pos_of_mem_pos _ hpos
    apply interval_eval_sound
    simp only [Membership.mem]
    apply Set.mem_of_subset_of_mem _ hx
    apply interior_subset


#check (toRealPoly p).eval
#check intermediate_value_Icc
#check intermediate_value_uIcc
#check Polynomial.toContinuousMap_apply
#check mul_neg_iff
#check Set.uIcc_of_le I.isValid'

-- p (I.left) * p (I.right)   (essentially)
abbrev LeftEval := (evalWithPrec prec p I.left.toRat)
abbrev RightEval := (evalWithPrec prec p I.right.toRat)

lemma eval_endpt_product_neg (h : (I.LeftEval prec p) * (I.RightEval prec p) < 0) :
  (toRealPoly p).eval (↑I.left.toRat) * (toRealPoly p).eval (↑I.right.toRat) < 0 := by
  grind only [neg_of_mem_neg, mul_sound, eval_sound]

lemma eval_endpt_product_pos (h : 0 < (I.LeftEval prec p) * (I.RightEval prec p)) :
  0 < (toRealPoly p).eval (↑I.left.toRat) * (toRealPoly p).eval (↑I.right.toRat) := by
  grind only [pos_of_mem_pos, mul_sound, eval_sound]

theorem hasroot_of_eval_endpts
  (h : (I.LeftEval prec p) * (I.RightEval prec p) < 0) :
  I.HasRoot p := by
  have h₀ : 0 ∈ (fun x ↦ eval x (toRealPoly p)) '' I.toSet := by
    have h' := eval_endpt_product_neg prec I p h
    rw [mul_neg_iff] at h'
    unfold toSet; rw [← Set.uIcc_of_le I.isValid']
    rcases h' with hleft | hright
    · apply intermediate_value_uIcc (Polynomial.continuousOn (toRealPoly p))
      apply Set.mem_uIcc_of_ge
      · grind only
      · grind only
    · apply intermediate_value_uIcc (Polynomial.continuousOn (toRealPoly p))
      apply Set.mem_uIcc_of_le
      · grind only
      · grind only
  simp only [Set.mem_image] at h₀
  unfold HasRoot; exact h₀

theorem has_unique_root_of_eval_endpts
  (h : (I.LeftEval prec p) * (I.RightEval prec p) < 0)
  (h' : I.StrictMonoOrStrictAnti p) : I.HasUniqueRoot p := by
  have h' := h'.elim StrictAntiOn.injOn StrictMonoOn.injOn
  apply existsUnique_of_exists_of_unique (hasroot_of_eval_endpts prec _ _ h)
  intro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
  rw [← Set.InjOn.eq_iff h' hx hy, hy', hx']

theorem has_no_root_of_eval_endpts
  (h : 0 < (I.LeftEval prec p) * (I.RightEval prec p))
  (h' : I.StrictMonoOrStrictAnti p): I.HasNoRoot p := by
  by_contra hf; simp only [hasNoRoot_iff_not_hasRoot, not_not] at hf
  obtain ⟨x, hx, hx'⟩ := hf
  have h := eval_endpt_product_pos prec I p h
  rw [mul_pos_iff] at h
  rcases h with hleft | hright
  · rcases h' with ha | hm
    · apply StrictAntiOn.antitoneOn at ha
      simp only [AntitoneOn] at ha
      have := ha hx (I.right_mem) hx.right
      rw [hx'] at this
      grind only
    · apply StrictMonoOn.monotoneOn at hm
      simp only [MonotoneOn] at hm
      have := hm (I.left_mem) hx hx.left
      rw [hx'] at this
      grind only
  · rcases h' with ha | hm
    · apply StrictAntiOn.antitoneOn at ha
      simp only [AntitoneOn] at ha
      have := ha (I.left_mem) hx hx.left
      rw [hx'] at this
      grind only
    · apply StrictMonoOn.monotoneOn at hm
      simp only [MonotoneOn] at hm
      have := hm hx (I.right_mem) hx.right
      rw [hx'] at this
      grind only

end PolynomialRoots
end DyadicInterval
