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
open Dyadic DyadicInterval Polynomial Set
variable (prec : ℤ) (I J: DyadicInterval) {n : ℕ} (p : RatPol n)

def HasRoot := ∃ x ∈ I, (toRealPoly p).eval x = 0

def HasNoRoot := ∀ x ∈ I, (toRealPoly p).eval x ≠ 0

def HasUniqueRoot := ∃! x ∈ I, (toRealPoly p).eval x = 0

theorem hasNoRoot_iff_not_hasRoot : I.HasNoRoot p ↔ ¬ (I.HasRoot p) := by
  simp only [HasNoRoot, HasRoot]
  simp only [mem_iff_mem_Icc, mem_Icc, ne_eq, and_imp, not_exists, not_and]

theorem hasRoot_of_hasUniqueRoot (h : I.HasUniqueRoot p) : I.HasRoot p := by
  simp only [HasUniqueRoot, HasRoot] at *
  apply ExistsUnique.exists; exact h

theorem hasNoRoot_subset (h : J ⊆ I) (h_no : I.HasNoRoot p) :
  J.HasNoRoot p := by
  intro x hx; apply h_no
  exact mem_of_subset_of_mem ((subset_iff J I).mp h) hx

theorem hasRoot_subset (h : J ⊆ I) (h_root : HasRoot J p) :
  I.HasRoot p := by
  simp only [HasRoot] at *
  obtain ⟨x, hx, hx'⟩ := h_root
  use x; constructor
  · exact  mem_of_subset_of_mem ((subset_iff J I).mp h) hx
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

theorem strict_mono_of_pos_deriv (h : 0 < intervalEvalWithPrec prec (deriv p) I) :
  StrictMonoOn (toRealPoly p).eval I := by
    apply strictMonoOn_of_deriv_pos (by apply convex_Icc) (by apply Polynomial.continuousOn)
    intro x hx
    simp only [Polynomial.deriv, ← deriv_eq_real_poly_deriv]
    apply pos_of_mem_pos _ h
    apply interval_eval_sound
    simp only [Membership.mem]
    apply mem_of_subset_of_mem _ hx
    apply interior_subset

theorem strict_anti_of_neg_deriv (h : intervalEvalWithPrec prec (deriv p) I < 0) :
  StrictAntiOn (toRealPoly p).eval I := by
    apply strictAntiOn_of_deriv_neg (by apply convex_Icc) (by apply Polynomial.continuousOn)
    intro x hx
    simp only [Polynomial.deriv, ← deriv_eq_real_poly_deriv]
    apply neg_of_mem_neg _ h
    apply interval_eval_sound
    simp only [Membership.mem]
    apply mem_of_subset_of_mem _ hx
    apply interior_subset

abbrev StrictMonoOrStrictAnti := StrictAntiOn (toRealPoly p).eval I ∨ StrictMonoOn (toRealPoly p).eval I

theorem strict_mono_of_deriv_zerofree (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I)) :
   I.StrictMonoOrStrictAnti p:= by
   grind only [ZeroFree, strict_anti_of_neg_deriv, strict_mono_of_pos_deriv]

theorem injOn_of_deriv_zerofree (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I)) :
  (I.toSet).InjOn (fun x ↦ eval x (toRealPoly p)) :=
  have h' := strict_mono_of_deriv_zerofree _ _ _ h
  h'.elim StrictAntiOn.injOn StrictMonoOn.injOn

-- Move all of this stuff out of here; preferably into "RationalPolynomials.Basic" -- pending refactor
-- p (I.left) * p (I.right)   (essentially)
abbrev LeftEval := (evalWithPrec prec p I.left.toRat)
abbrev RightEval := (evalWithPrec prec p I.right.toRat)
noncomputable abbrev LeftEval' := (toRealPoly p).eval ↑I.left.toRat
noncomputable abbrev RightEval' := (toRealPoly p).eval ↑I.right.toRat
noncomputable abbrev MidEval' := (toRealPoly p).eval ↑I.midpoint.toRat

theorem increasing_of_pos_deriv (h : 0 < intervalEvalWithPrec prec (deriv p) I) :
  I.LeftEval' p ≤ I.MidEval' p ∧ I.MidEval' p ≤ I.RightEval' p := by
  apply strict_mono_of_pos_deriv at h
  apply StrictMonoOn.monotoneOn at h
  have h₁ := h I.left_mem I.midpoint_mem (I.midpoint_mem).left
  have h₂ := h I.midpoint_mem I.right_mem (I.midpoint_mem).right
  exact ⟨h₁, h₂⟩

theorem decreasing_of_neg_deriv (h : intervalEvalWithPrec prec (deriv p) I < 0) :
  I.RightEval' p ≤ I.MidEval' p ∧ I.MidEval' p ≤ I.LeftEval' p := by
  apply strict_anti_of_neg_deriv at h
  apply StrictAntiOn.antitoneOn at h
  have h₁ := h I.midpoint_mem I.right_mem (I.midpoint_mem).right
  have h₂ := h I.left_mem I.midpoint_mem (I.midpoint_mem).left
  exact ⟨h₁, h₂⟩

lemma eval_endpt_product_neg (h : (I.LeftEval prec p) * (I.RightEval prec p) < 0) :
  I.LeftEval' p * I.RightEval' p < 0 := by
  grind only [neg_of_mem_neg, mul_sound, eval_sound]

lemma eval_endpt_product_pos (h : 0 < (I.LeftEval prec p) * (I.RightEval prec p)) :
  0 < I.LeftEval' p * I.RightEval' p := by
  grind only [pos_of_mem_pos, mul_sound, eval_sound]

theorem eval_endpts_of_has_root
  (h : (I.LeftEval prec p) * (I.RightEval prec p) < 0) :
  I.HasRoot p := by
  have h₀ : 0 ∈ (fun x ↦ eval x (toRealPoly p)) '' I.toSet := by
    have h' := eval_endpt_product_neg prec I p h
    rw [mul_neg_iff] at h'
    unfold toSet; rw [← uIcc_of_le I.isValid']
    rcases h' with hleft | hright
    · apply intermediate_value_uIcc (Polynomial.continuousOn (toRealPoly p))
      apply mem_uIcc_of_ge
      · grind only
      · grind only
    · apply intermediate_value_uIcc (Polynomial.continuousOn (toRealPoly p))
      apply mem_uIcc_of_le
      · grind only
      · grind only
  simp only  [mem_image] at h₀
  unfold HasRoot; exact h₀

theorem eval_endpts_of_has_unique_root
  (h : (I.LeftEval prec p) * (I.RightEval prec p) < 0)
  (h' : I.StrictMonoOrStrictAnti p) : I.HasUniqueRoot p := by
  have h' := h'.elim StrictAntiOn.injOn StrictMonoOn.injOn
  apply existsUnique_of_exists_of_unique (eval_endpts_of_has_root prec _ _ h)
  intro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
  rw [← InjOn.eq_iff h' hx hy, hy', hx']

theorem eval_endpts_of_has_no_root
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

section NewtonMethod
open Dyadic DyadicInterval Polynomial Set
variable (prec : ℤ) (I J: DyadicInterval) {n : ℕ} (p : RatPol n)

-- N(I) := I.m - p(m)/p'(I)
def Newton := I.midpoint - divWithPrec prec (evalWithPrec prec p I.midpoint.toRat)
  (I.intervalEvalWithPrec prec (deriv p))

theorem mem_newton (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I)) : ∀ c ∈ I,
  ↑I.midpoint.toRat - eval (↑I.midpoint.toRat) (toRealPoly p) / eval c (toRealPoly (deriv p)) ∈ (I.Newton prec p):= by
  intro c hc; unfold Newton
  apply sub_sound _ _ _ (to_rat_mem_of_dyadic I.midpoint)
  grind only [div_sound, eval_sound, interval_eval_sound]

theorem has_root_of_newton_has_root (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I))
  {x : ℝ} (hx : x ∈ I) : (toRealPoly p).eval x = 0 → x ∈ (I.Newton prec p) := by
  intro hx'; obtain ⟨ξ, hξ, hξ'⟩ := mvt_real_poly p I x hx
  have h₀ : (eval ξ (toRealPoly (deriv p))) ≠ 0 := by
    apply mem_zerofree_neq_zero _ h
    apply interval_eval_sound _ _ _ _ hξ
  have : x = ↑I.midpoint.toRat - (eval (↑I.midpoint.toRat) (toRealPoly p)) /  (eval ξ (toRealPoly (deriv p))) :=
    by grind only
  grind only [Newton, sub_sound, to_rat_mem_of_dyadic, div_sound, eval_sound, interval_eval_sound]

theorem pos_deriv_of_newton_subset_of_has_root (h : 0 < intervalEvalWithPrec prec (deriv p) I)
  (h' : (I.Newton prec p) ⊆ I) : I.HasRoot p := by
  rw [subset_iff_endpts] at h'
  have : 0 ∈ (fun x ↦ eval x (toRealPoly p))'' I.toSet := by
    apply intermediate_value_Icc I.isValid' (Polynomial.continuousOn (toRealPoly p))
    have := increasing_of_pos_deriv prec I p h
    have h₁ : ∀ c ∈ I, 0 < (toRealPoly (deriv p)).eval c := by
      intro c hc; apply pos_of_mem_pos _ h _ (interval_eval_sound prec (deriv p) I c hc)
    rcases le_total 0 (I.MidEval' p) with h₀ | h₀
    · refine ⟨?_, le_trans h₀ this.right⟩
      obtain ⟨c, hc, hc'⟩ := mvt_real_poly p I _ I.left_mem; rw [hc']
      rw [← le_neg_iff_add_nonpos_right, ← le_div_iff₀' (h₁ _ hc), neg_div, sub_le_iff_le_add,
        _root_.add_comm, ← sub_eq_add_neg (I.midpoint.toRat : ℝ)]
      have h'' := (mem_newton prec I p (pos_zerofree _ h) c hc).left
      apply le_trans _ h''; norm_cast
      rw [← le_iff_toRat]; exact h'.left

    · refine ⟨le_trans this.left h₀, ?_⟩
      obtain ⟨c, hc, hc'⟩ := mvt_real_poly p I _ I.right_mem; rw[hc']
      rw [← neg_le_iff_add_nonneg, _root_.mul_comm, ← div_le_iff₀ (h₁ _ hc), neg_div, le_sub_iff_add_le,
        _root_.add_comm, ← sub_eq_add_neg (I.midpoint.toRat : ℝ)]
      have h'' := (mem_newton prec I p (pos_zerofree _ h) c hc).right
      apply le_trans h''; norm_cast
      rw [← le_iff_toRat]; exact h'.right

  simp only [mem_image] at this
  unfold HasRoot; exact this

theorem neg_deriv_of_newton_subset_of_has_root (h : intervalEvalWithPrec prec (deriv p) I < 0)
  (h' : (I.Newton prec p) ⊆ I) : I.HasRoot p := by
  have : 0 ∈ (fun x ↦ eval x (toRealPoly p))'' I.toSet := by
    unfold toSet; rw [← uIcc_of_le I.isValid']
    apply intermediate_value_uIcc (Polynomial.continuousOn (toRealPoly p))
    have := decreasing_of_neg_deriv prec I p h
    have h₁ : ∀ c ∈ I, 0 < - (toRealPoly (deriv p)).eval c := by
      intro c hc; simp only [Left.neg_pos_iff]
      apply neg_of_mem_neg _ h _ (interval_eval_sound prec (deriv p) I c hc)
    rw [uIcc_of_ge (le_trans this.left this.right)]
    rcases le_total 0 (I.MidEval' p) with h₀ | h₀
    · refine ⟨?_, le_trans h₀ this.right⟩
      obtain ⟨c, hc, hc'⟩ := mvt_real_poly p I _ I.right_mem; simp only [hc']
      rw [← neg_neg (eval c (toRealPoly (deriv p))), _root_.neg_mul]
      rw [← le_neg_iff_add_nonpos_right, neg_le_neg_iff, _root_.mul_comm, ← div_le_iff₀ (h₁ _ hc), div_neg]
      rw [le_sub_iff_add_le, _root_.add_comm, ← sub_eq_add_neg (I.midpoint.toRat : ℝ)]
      have h'' := (mem_newton prec I p (neg_zerofree _ h) c hc).right
      apply le_trans h''; norm_cast
      rw [← le_iff_toRat]; exact h'.right

    · refine ⟨le_trans this.left h₀, ?_⟩
      obtain ⟨c, hc, hc'⟩ := mvt_real_poly p I _ I.left_mem; simp only [hc']
      rw [← neg_neg (eval c (toRealPoly (deriv p))), _root_.neg_mul]
      rw [← neg_le_iff_add_nonneg, neg_le_neg_iff, ← le_div_iff₀' (h₁ _ hc), div_neg, sub_le_iff_le_add]
      rw [_root_.add_comm, ← sub_eq_add_neg (I.midpoint.toRat : ℝ)]
      have h'' := (mem_newton prec I p (neg_zerofree _ h) c hc).left
      apply le_trans _ h''; norm_cast
      rw [← le_iff_toRat]; exact h'.left
  simp only [mem_image] at this
  unfold HasRoot; exact this

theorem newton_subset_of_has_root (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I))
  (h' : (I.Newton prec p) ⊆ I) : I.HasRoot p := by
  grind only [ZeroFree, neg_deriv_of_newton_subset_of_has_root, pos_deriv_of_newton_subset_of_has_root]

theorem newton_subset_of_has_unique_root (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I))
  (h' : (I.Newton prec p) ⊆ I) : I.HasUniqueRoot p := by
  have h'' := injOn_of_deriv_zerofree _ _ _ h
  apply existsUnique_of_exists_of_unique (newton_subset_of_has_root _ _ _ h h')
  intro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
  rw [← InjOn.eq_iff h'' hx hy, hy', hx']

theorem newton_disjoint_of_has_no_root (h : ZeroFree (intervalEvalWithPrec prec (deriv p) I))
  (h' : I ⊓ (I.Newton prec p) = none) : I.HasNoRoot p := by
  by_contra hf; rw [hasNoRoot_iff_not_hasRoot, not_not] at hf
  obtain ⟨x, hx, hx'⟩ := hf
  have hx'' := has_root_of_newton_has_root prec I p h hx hx'
  have h' := inter_toSet_none _ _ h'; rw [← disjoint_iff_inter_eq_empty] at h'
  have : ¬Disjoint I.toSet (Newton prec I p).toSet := by
    rw [not_disjoint_iff_nonempty_inter, Set.inter_nonempty]
    use x; exact ⟨hx, hx''⟩
  grind only

end NewtonMethod
end DyadicInterval
