import Mathlib
import Krawcheck.DyadicIntervals
import Krawcheck.PolynomialBounds
import Krawcheck.PolynomialRoots

-- Specify import later
-- set_option diagnostics true
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false

namespace Vector
open Vector

lemma zip_push {α : Type _} {n : ℕ} {β : Type _} {as : Vector α n} {bs : Vector β n}
  {a : α} {b : β} :
  zip (as.push a) (bs.push b) = (zip as bs).push (a,b) := by
  simp only [← append_singleton, zip_append]
  simp only [mk_zip_mk, List.zip_toArray, List.zip_cons_cons, List.zip_nil_right, append_singleton]

theorem ofFn_get {α : Type _} {n : ℕ} (v : Vector α n) : ofFn (v.get) = v := by
  ext i hi; simp only [getElem_ofFn, get_eq_getElem]

end Vector

/-- List of Coeff, Monomial pairs; where monomial is represented by its power in each variable; ℝ^k → ℝ -/
abbrev MvRatPol (n : ℕ) := List (ℚ × Vector ℕ n)

namespace MvRatPol
section Structural
open DyadicInterval Dyadic Vector MvPolynomial
variable {m n : ℕ}

-- Given a coefficeient a and multi-index; constructs a ⬝ x^i
noncomputable def toMvMono (q : ℚ × Vector ℕ n) : MvPolynomial (Fin n) ℚ :=
  -- Finset.univ = {0, 1,..., k-1}
  -- The third term is the proof, ∀ (i : Fin n), powers.get i ≠ 0 → i ∈ Finset.univ
  let f' := Finsupp.onFinset Finset.univ (q.2.get) (fun i _ => Finset.mem_univ i)
  monomial f' q.1   --f' is the Finite support version of powers.get

noncomputable def toMvRealMono (q : ℚ × Vector ℕ n) : MvPolynomial (Fin n) ℝ :=
  (toMvMono q).map (algebraMap ℚ ℝ)

noncomputable def toMvPoly (p : MvRatPol n) : MvPolynomial (Fin n) ℚ :=
  (p.map fun q ↦ toMvMono q).sum

-- noncomputable def ofMvPoly (p : MvPolynomial (Fin n) ℚ): MvRatPol n :=
--   let support := p.support.toList
--   support.map (fun m => (p.coeff m, Vector.ofFn m))

lemma to_mv_poly_mono (q : ℚ × Vector ℕ n) : toMvPoly [q] = toMvMono q := by
  simp only [toMvPoly, toMvMono, List.map_singleton, List.sum_singleton]

noncomputable def toMvRealPoly (p : MvRatPol n) : MvPolynomial (Fin n) ℝ :=
  (toMvPoly p).map (algebraMap ℚ ℝ)

lemma to_mv_real_poly_mono (q : ℚ × Vector ℕ n) : toMvRealPoly [q] = toMvRealMono q := by
  simp only [toMvRealMono, toMvRealPoly]; congr 1
  simp only [to_mv_poly_mono]

def C (n : ℕ) (q : ℚ)  : MvRatPol n := [(q, 0)]

instance : Zero (MvRatPol n) := ⟨C n 0⟩
instance : One (MvRatPol n) := ⟨C n 1⟩

theorem to_mv_poly_C (n : ℕ) (q : ℚ) : toMvPoly (C n q) = MvPolynomial.C q := by
  simp only [C, to_mv_poly_mono, toMvMono]
  have : Finsupp.onFinset Finset.univ (Vector.get (0 : Vector ℕ n)) (fun i _ => Finset.mem_univ i) = 0 := by
    ext i; simp only [Finsupp.onFinset_apply, Finsupp.coe_zero, Pi.zero_apply]
    change Vector.get (replicate n 0) i = 0
    simp only [get_replicate]
  rw [this, ← MvPolynomial.C_apply]

theorem to_mv_poly_zero (n : ℕ) : toMvPoly (0 : MvRatPol n) = 0 := by
  change toMvPoly (C n 0) = 0
  simp only [to_mv_poly_C, C_0]

theorem to_mv_poly_one (n : ℕ) : toMvPoly (1 : MvRatPol n) = 1 := by
  change toMvPoly (C n 1) = 1
  simp only [to_mv_poly_C, C_1]

theorem to_mv_real_poly_C (n : ℕ) (q : ℚ) : toMvRealPoly (C n q) = MvPolynomial.C ↑q := by
  simp only [toMvRealPoly, to_mv_poly_C, map_C, eq_ratCast]

def X (i : Fin n) : MvRatPol n := [(1, set 0 i 1)]

theorem to_mv_poly_X (i : Fin n) : toMvPoly (X i) = MvPolynomial.X i := by
  simp only [X, to_mv_poly_mono, toMvMono]
  have := @MvPolynomial.X_pow_eq_monomial ℚ (Fin n) 1 i _
  simp only [pow_one] at this; rw[this]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, monomial_left_inj]
  ext j; by_cases h : j = i
  · obtain ⟨i', hi⟩ := i
    simp only [h, Finsupp.onFinset_apply, Finsupp.single_eq_same]
    simp only [get_eq_getElem, getElem_set_self]
  · simp only [Finsupp.onFinset_apply, ne_eq, h, not_false_eq_true, Finsupp.single_eq_of_ne]
    have : (i : ℕ) ≠ j := by grind only
    rw [get_eq_getElem, getElem_set_ne _ _ this]
    rw [← get_eq_getElem]
    change Vector.get (replicate n 0) j = 0
    simp only [get_replicate]

theorem to_mv_real_poly_X (i : Fin n) : toMvRealPoly (X i) = MvPolynomial.X i := by
  simp only [toMvRealPoly, to_mv_poly_X, map_X]

lemma to_mv_mono_const (q : ℚ × Vector ℕ 0) : toMvMono q = MvPolynomial.C q.1 := by
  simp only [toMvMono, Finset.univ_eq_empty]
  have h_zero : Finsupp.onFinset ∅ q.2.get (fun i _ => Finset.mem_univ i) = 0 := Subsingleton.elim _ _
  rw [h_zero, ← MvPolynomial.C_apply]

lemma to_mv_real_mono_const (q : ℚ × Vector ℕ 0) : toMvRealMono q = MvPolynomial.C ↑q.1 := by
  grind only [toMvRealMono, to_mv_mono_const, map_C, eq_ratCast]

-- lemma to_mv_mono_push (c : ℚ) (as : Vector ℕ n) (a : ℕ) : toMvMono (c, as.push a)

lemma to_mv_poly_cons (q : ℚ × Vector ℕ n)(qs : MvRatPol n) :
  toMvPoly (q :: qs) = toMvMono q + toMvPoly qs := by
  simp only [toMvPoly, List.map_cons, List.sum_cons]

lemma to_mv_real_poly_cons (q : ℚ × Vector ℕ n)(qs : MvRatPol n) :
  toMvRealPoly (q :: qs) = toMvRealMono q + toMvRealPoly qs := by
  grind only [toMvRealPoly, to_mv_poly_cons, map_add, toMvRealMono]

def coeff (p : MvRatPol n) (m : Fin n →₀ ℕ) : ℚ :=
  let m_vec := Vector.ofFn m                   -- Convert monomial to a vector
  let p' := p.filter (fun q ↦ q.2 = m_vec)     -- Filter all monomials
  (p'.map (fun q ↦ q.1)).sum                   -- Get coeffs and add

lemma coeff_trivial (m : Fin n →₀ ℕ) : coeff [] m = 0 := by
  simp only [coeff, List.filter_nil, List.map_nil, List.sum_nil]

lemma coeff_mono (q : ℚ × Vector ℕ n) (m : Fin n →₀ ℕ) :
  coeff [q] m = if q.2 = ofFn m then q.1 else 0 := by
  split_ifs with h
  · simp only [coeff, h, decide_true, List.filter_cons_of_pos, List.filter_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, _root_.add_zero]
  · simp only [coeff, h, decide_false, Bool.false_eq_true, not_false_eq_true,
    List.filter_cons_of_neg, List.filter_nil, List.map_nil, List.sum_nil]

lemma coeff_to_mv_mono (q : ℚ × Vector ℕ n) (m : Fin n →₀ ℕ) :
  coeff [q] m = MvPolynomial.coeff m (toMvMono q) := by
  rw [coeff_mono]
  have :
    q.2 = ofFn ⇑m ↔ Finsupp.onFinset Finset.univ q.2.get (fun i _ => Finset.mem_univ i) = m := by
    constructor <;> intro h
    · have : (ofFn ⇑m).get = ⇑m := by ext i; simp only [get_ofFn]
      simp only [h, this]; grind only [= Finsupp.onFinset_apply, #4967, #547e]
    · have : ofFn q.2.get = q.2 := by
        ext i hi; simp only [getElem_ofFn, get_eq_getElem]
      rw [← this]; congr; rw [← h]
      grind only [= Finsupp.onFinset_apply, #4967, #d894]

  split_ifs with h
  <;> simp only [toMvMono, coeff_monomial]
  <;> rw [this] at h
  <;> simp only [h, ↓reduceIte]

lemma coeff_cons (q : ℚ × Vector ℕ n)(qs : MvRatPol n) (m : Fin n →₀ ℕ) :
  coeff (q :: qs) m = coeff [q] m + coeff qs m := by
  rw [coeff_mono]; split_ifs with h
  · simp only [coeff, List.filter_cons]
    simp only [h, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
  · simp only [coeff, List.filter_cons]
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, _root_.zero_add]

lemma coeff_to_mv_poly (p : MvRatPol n) (m : Fin n →₀ ℕ) : p.coeff m = (p.toMvPoly).coeff m := by
  induction p with
  | nil =>
    grind only [coeff, toMvPoly, List.filter_nil, List.map_nil, List.sum_nil, coeff_zero]
  | cons q qs ih =>
    simp only [to_mv_poly_cons, coeff_add]
    rw [coeff_cons, ih]; simp only [coeff_to_mv_mono]

lemma coeff_to_mv_real_poly (p : MvRatPol n) (m : Fin n →₀ ℕ) : p.coeff m  = (p.toMvRealPoly).coeff m := by
  simp only [coeff_to_mv_poly, toMvRealPoly, coeff_map, eq_ratCast]

lemma to_mv_poly_trivial (p : MvRatPol n) : p = [] → toMvPoly p = 0 := by
  intro h; ext m
  simp only [coeff_zero, ← coeff_to_mv_poly]
  simp only [coeff, h, List.filter_nil, List.map_nil, List.sum_nil]

lemma to_mv_real_poly_trivial (p : MvRatPol n) : p = [] → toMvRealPoly p = 0 := by
  intro h; ext m
  simp only [coeff_zero, ← coeff_to_mv_real_poly]; norm_cast
  simp only [coeff, h, List.filter_nil, List.map_nil, List.sum_nil]

end Structural

section Evaluation
open DyadicInterval Dyadic Vector MvPolynomial
variable {m n : ℕ}

def evalMonomial (q : ℚ × Vector ℕ n) (x : Vector ℚ n) : ℚ :=
  let vs₀ := zip x q.2
  let vs := vs₀.map (fun (z,n) ↦ z^n)
  foldr (· * ·) (q.1) vs

lemma eval_mono_const (q : ℚ × Vector ℕ 0) (x : Vector ℚ 0) :
  evalMonomial q x = q.1 := by
  simp only [evalMonomial, Vector.eq_empty, foldr_mk, List.size_toArray, List.length_nil,
    List.foldr_toArray', List.foldr_nil]

lemma eval_push_pop_back' (q : ℚ × Vector ℕ (n + 1)) (x : Vector ℚ (n + 1)) :
  (eval x.get) (toMvMono q) = (eval (x.pop).get) (toMvMono (q.1, q.2.pop)) * x.back ^ q.2.back := by
  simp only [toMvMono, eval_monomial]
  simp only [Finsupp.prod_pow, Finsupp.onFinset_apply, Nat.add_one_sub_one]
  rw [_root_.mul_assoc]; congr
  rw [Fin.prod_univ_castSucc]; congr
  simp only [get_pop]

lemma eval_monomial_sound (q : ℚ × Vector ℕ n) (x : Vector ℚ n) :
  (toMvMono q).eval x.get = evalMonomial q x := by
  induction n with
  | zero =>
    simp only [to_mv_mono_const, eval_C, eval_mono_const]
  | succ m  ih=>
    simp only [evalMonomial]
    rw [←push_pop_back x, ← push_pop_back q.2]
    simp only [zip_push, map_push, foldr_push]
    rw [_root_.mul_comm, foldr_assoc]
    rw [eval_push_pop_back' q _, push_pop_back]
    simp only [Nat.add_one_sub_one]
    specialize ih (q.1, q.2.pop) x.pop
    simp only [ih, evalMonomial]

def evalWithPrec (prec : ℤ) (p : MvRatPol n) (x : Vector ℚ n) : DyadicInterval :=
  let rat_eval := (p.map (fun q ↦ evalMonomial q x)).sum
  ofRatWithPrec prec rat_eval

theorem eval_sound (prec : ℤ) (p : MvRatPol n) (x : Vector ℚ n) :
  (toMvRealPoly p).eval (fun i ↦ ↑(x.get i)) ∈ evalWithPrec prec p x := by
  simp only [evalWithPrec]
  have :  (eval fun i ↦ ↑(x.get i)) p.toMvRealPoly =
    (List.map (fun q ↦ evalMonomial q x) p).sum := by
    simp only [toMvRealPoly, toMvPoly, eval_map]
    induction p with
    | nil =>
      simp only [List.map_nil, List.sum_nil, eval₂_zero, Rat.cast_zero]
    | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons, eval₂_add, Rat.cast_add, ih, add_left_inj]
      have : ↑((eval x.get) (toMvMono q)) = (algebraMap ℚ ℝ) (eval x.get (toMvMono q)) := by rfl
      rw [← (eval_monomial_sound q x), ← eval_map, this]
      simp only [map_eval]; congr
  grind only [rat_mem_of_rat]

-- This must be foldr and not prod because we don't have CommMonoid DyadicInterval
def vectervalEvalMonomial (prec : ℤ) (q : ℚ × Vector ℕ n) (X : Vecterval n) :
  DyadicInterval :=
  let vs₀ := zip X q.2
  let vs := Vector.map (fun (z,n) ↦ z^n) vs₀
  foldr (· * ·) (ofRatWithPrec prec q.1) vs

lemma vecterval_eval_mono_const (prec : ℤ) (q : ℚ × Vector ℕ 0) (X : Vecterval 0) :
  vectervalEvalMonomial prec q X = ofRatWithPrec prec q.1 := by
  simp only [vectervalEvalMonomial, Vecterval.eq_empty, foldr_mk, List.size_toArray,
    List.length_nil, List.foldr_toArray', List.foldr_nil]

-- Evaluate as a sum of monomials
def vectervalEvalWithPrec (prec : ℤ) (p : MvRatPol n) (X : Vecterval n) : DyadicInterval :=
  (p.map fun q ↦ vectervalEvalMonomial prec q X).sum

lemma eval_push_pop_back (prec : ℤ) (q : ℚ × Vector ℕ (n + 1)) (X : Vecterval (n + 1)) : ∀ x ∈ X,
  (eval x.get) (toMvRealMono q) = (eval (x.pop).get) (toMvRealMono (q.1, q.2.pop)) * x.back ^ q.2.back := by
  intro x hx; simp only [toMvRealMono, toMvMono, map_monomial, eval_monomial]
  simp only [eq_ratCast, Finsupp.prod_pow, Finsupp.onFinset_apply, Nat.add_one_sub_one]
  rw [_root_.mul_assoc]; congr
  rw [Fin.prod_univ_castSucc]; congr
  simp only [get_pop]

theorem vecterval_eval_monomial_sound (prec : ℤ) (q : ℚ × Vector ℕ n) (X : Vecterval n) :
  ∀ x ∈ X, (toMvRealMono q).eval x.get ∈ vectervalEvalMonomial prec q X := by
  induction n with
  | zero =>
    grind only [to_mv_real_mono_const, eval_C, vecterval_eval_mono_const, rat_mem_of_rat]
  | succ n ih =>
    intro x hx
    simp only [vectervalEvalMonomial]
    rw [←push_pop_back X, ← push_pop_back q.2]
    simp only [zip_push, map_push, foldr_push]
    rw [DyadicInterval.mul_comm, foldr_assoc]
    rw [eval_push_pop_back prec q X _ hx]
    apply mul_sound
    · apply ih (q.1, q.2.pop) X.pop x.pop
      exact Vecterval.mem_pop_of_mem _ _ hx
    · apply pow_sound _ _ _
      exact Vecterval.mem_back_of_mem _ _ hx

theorem vecterval_eval_sound (prec : ℤ) (p : MvRatPol n) (X : Vecterval n) :
  ∀ x ∈ X, (toMvRealPoly p).eval x.get ∈ vectervalEvalWithPrec prec p X := by
  induction p with
  | nil =>
    simp only [← MvPolynomial.eval₂_id, vectervalEvalWithPrec, List.map_nil, List.sum_nil,
      to_mv_real_poly_trivial, MvPolynomial.eval₂_zero]
    simp only [mem_iff_le_endpts, left_coe_zero, toRat_zero, Rat.cast_zero,
      le_refl, right_coe_zero, and_self, implies_true]

  | cons q qs ih =>
    simp only [vectervalEvalWithPrec, List.map_cons, List.sum_cons, to_mv_real_poly_cons, eval_add]
    intro x hx; apply add_sound
    · grind only [vecterval_eval_monomial_sound]
    · grind only [vectervalEvalWithPrec]

end Evaluation

section Derivative
open DyadicInterval Dyadic Vector MvPolynomial
variable {m n : ℕ}

def pderivMono (i : Fin n) (coeff : ℚ) (powers : Vector ℕ n) : ℚ × Vector ℕ n :=
  let p := powers.get i
  if p = 0 then (0, 0)
  else ⟨(coeff * p), powers.set i (p-1)⟩

def pderiv (i : Fin n) (p : MvRatPol n) : MvRatPol n := p.map (fun (a, xs) ↦ pderivMono i a xs)
  -- simp only [pderiv, List.map_cons, List.map_nil]; rfl

theorem pderiv_mono (i : Fin n) (x : Fin n → ℝ) (q : ℚ × Vector ℕ n) : (eval x) (pderiv i [q]).toMvRealPoly =
  ↑q.1 * ((∏ j ∈ Finset.univ.erase i, x j ^ q.2.get j) * (↑(q.2.get i) * x i ^ (q.2.get i - 1))) := by
  simp only [pderiv, pderivMono, List.map_cons, List.map_nil, to_mv_real_poly_mono]
  split_ifs with h
  · simp only [h, CharP.cast_eq_zero, zero_tsub, pow_zero, _root_.mul_one, MulZeroClass.mul_zero]
    simp only [toMvRealMono, toMvMono, map_zero]
  · simp only [toMvRealMono, toMvMono, map_monomial, eq_ratCast, Rat.cast_mul, Rat.cast_natCast,
    eval_monomial, Finsupp.prod_pow, Finsupp.onFinset_apply]
    simp only [_root_.mul_assoc, mul_eq_mul_left_iff, Rat.cast_eq_zero]; left
    rw [← _root_.mul_assoc (∏ j ∈ Finset.univ.erase i, x j ^ q.2.get j),
        _root_.mul_comm (∏ j ∈ Finset.univ.erase i, x j ^ q.2.get j),
        _root_.mul_assoc _ (∏ j ∈ Finset.univ.erase i, x j ^ q.2.get j),
        _root_.mul_comm _ (x i ^ (q.2.get i - 1))]
    simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero, h, or_false]
    --simp only [get_eq_getElem, getElem_set, pow_ite]
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i) (fun j ↦ x j ^ (q.2.set i (q.2.get i - 1)).get j)]
    simp only [get_eq_getElem, getElem_set_self, mul_eq_mul_left_iff, Finset.sdiff_singleton_eq_erase]; left
    apply Finset.prod_congr (by rfl); intro j hj; congr 1
    simp only [getElem_set]; split_ifs with h'
    · replace h' := Fin.ext h'
      exfalso; grind only [= Finset.mem_erase]
    · rfl

lemma pderiv_cons_toMvRealPoly (i : Fin n) (q : ℚ × Vector ℕ n)(qs : MvRatPol n) :
  (pderiv i (q :: qs)).toMvRealPoly = (pderiv i [q]).toMvRealPoly + (pderiv i qs).toMvRealPoly := by
  simp [pderiv, List.map_cons, List.map_nil, to_mv_real_poly_cons, to_mv_real_poly_trivial]

theorem pderiv_C (i : Fin n) (c : ℚ) : pderiv i (C n c) = 0 := by
  simp only [pderiv, C, List.map_cons, List.map_nil, pderivMono]
  have : replicate n 0 = 0 := by rfl
  simp only [← this, get_replicate, ↓reduceIte]; rfl

theorem pderiv_zero (i : Fin n) : pderiv i 0 = 0 := by
  change pderiv i (C n 0) = 0
  simp only [pderiv_C]

theorem pderiv_X (i j : Fin n) :
  pderiv i (MvRatPol.X j) = if i = j then 1 else 0 := by
  simp only [pderiv, pderivMono, X, List.map_cons, _root_.one_mul, List.map_nil]
  split_ifs with h₁ h₂ h₂
  · grind only [get_eq_getElem, getElem_set_self, one_ne_zero]
  · rfl
  · have : replicate n 0 = 0 := rfl
    simp only [h₂, get_eq_getElem, getElem_set_self, Nat.cast_one, tsub_self, set_set]
    simp only [← this, set_replicate_self]; rfl
  · exfalso
    have h₂' : j.val ≠ i.val := by grind only
    have : replicate n 0 = 0 := rfl
    simp only [← this, get_eq_getElem] at h₁
    have h₁' := @getElem_set_ne _ _ j.val i.val (replicate n 0) 1 j.isLt i.isLt h₂'
    simp only [getElem_replicate] at h₁'
    grind only

/-- Frechet derivative is the linear map from ℝ^n → ℝ
  fderiv p x.get y = ∇p(x) · y = Σ i, ((∂p/∂xᵢ)(x)) * yᵢ -/
noncomputable def fderiv (p : MvRatPol n) (f : Fin n → ℝ) : StrongDual ℝ ((Fin n) → ℝ) :=
  let grad_eval (i : Fin n) : ℝ := (toMvRealPoly (pderiv i p)).eval f
  LinearMap.toContinuousLinearMap (∑ i : Fin n, grad_eval i • LinearMap.proj i)

theorem fderiv_trivial (x : Fin n → ℝ) : fderiv [] x = 0 := by
  simp only [fderiv, pderiv, List.map_nil, to_mv_real_poly_trivial,
    _root_.zero_smul, Finset.sum_const_zero, map_zero]

theorem fderiv_cons (x : Fin n → ℝ) (q : ℚ × Vector ℕ n)(qs : MvRatPol n) :
  fderiv (q :: qs) x = fderiv [q] x + fderiv qs x := by
  simp only [fderiv, map_sum, map_smul, ← Finset.sum_add_distrib]; congr 1
  ext i v; rw [pderiv_cons_toMvRealPoly]
  simp only [eval_add, ContinuousLinearMap.coe_smul',
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_proj, Pi.smul_apply, Function.eval,
    smul_eq_mul, ContinuousLinearMap.add_apply]
  grind only

theorem fderiv_mono (x : Fin n → ℝ) (q : ℚ × Vector ℕ n) :
  fderiv [q] x = ↑q.1 • (∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, x j ^ q.2.get j)
  • (q.2.get i • x i ^ (q.2.get i - 1)) • ContinuousLinearMap.proj i) := by
  ext v
  simp only [fderiv, map_sum, map_smul, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_proj, Finset.sum_apply, Pi.smul_apply,
    Function.eval, smul_eq_mul, nsmul_eq_mul, ContinuousLinearMap.proj_apply, Rat.smul_def, Finset.mul_sum]
  congr; ext i
  rw [← _root_.mul_assoc (∏ j ∈ Finset.univ.erase i, x j ^ q.2.get j), ← _root_.mul_assoc]
  simp only [pderiv_mono]

theorem fderiv_zero (f : Fin n → ℝ) : fderiv 0 f = 0 := by
  simp only [fderiv, toMvRealPoly, pderiv_zero, to_mv_poly_zero, map_zero, _root_.zero_smul,
    Finset.sum_const_zero]

theorem fderiv_X (j : Fin n) (f : Fin n → ℝ) :
  fderiv (MvRatPol.X j) f = ContinuousLinearMap.proj j := by
  simp only [fderiv, pderiv_X, map_sum, map_smul]
  simp only [toMvRealPoly, apply_ite, to_mv_poly_one, to_mv_poly_zero, map_one, map_zero, ite_smul,
    one_smul, _root_.zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

theorem hasDerivWithinAt_mono (q : ℚ × Vector ℕ n) (X : Vecterval n) : ∀ x ∈ X.toSet,
  HasFDerivWithinAt (fun x ↦ (eval x) (toMvRealMono q)) (fderiv [q] x) X.toSet x := by
  intro x hx
  simp only [toMvRealMono, toMvMono, map_monomial, eq_ratCast, eval_monomial]
  simp only [Finsupp.prod_pow, Finsupp.onFinset_apply, fderiv_mono]
  apply HasFDerivWithinAt.const_mul
  apply HasFDerivWithinAt.finset_prod; intro i hi
  apply HasFDerivWithinAt.pow
  apply hasFDerivWithinAt_apply

theorem hasFDerivWithinAt_eval (p : MvRatPol n) (X : Vecterval n) : ∀ x ∈ X.toSet,
  HasFDerivWithinAt ((toMvRealPoly p).eval ·) (fderiv p x) X.toSet x := by
  intro x hx
  induction p with
  | nil =>
    simp only [to_mv_real_poly_trivial, ← eval₂_id, eval₂_zero, fderiv_trivial]
    change HasFDerivWithinAt 0 0 X.toSet x
    simp only [hasFDerivWithinAt_zero]

  | cons q qs ih =>
    simp only [to_mv_real_poly_cons, eval_add]
    rw [fderiv_cons]
    apply HasFDerivWithinAt.add _ ih
    exact hasDerivWithinAt_mono q X x hx

theorem mvt_real_poly (p : MvRatPol n) (X : Vecterval n) : ∀ x ∈ X, ∃ ξ ∈ X,
  (toMvRealPoly p).eval x.get = (toMvRealPoly p).eval X.midpoint_real.get +
  (p.fderiv ξ.get) (x.get - X.midpoint_real.get) := by
  intro x hx
  rw [Vecterval.mem_iff_get_mem_toSet] at hx
  have hxm := X.midpoint_mem
  rw [Vecterval.mem_iff_get_mem_toSet] at hxm
  obtain ⟨ξ, h, h'⟩ := domain_mvt (hasFDerivWithinAt_eval p X) X.convex hxm hx
  have : (ofFn ξ).get = ξ := by grind only [get_ofFn]
  use ofFn ξ; constructor
  · rw [Vecterval.mem_iff_get_mem_toSet, this]
    exact Set.mem_of_subset_of_mem (Convex.segment_subset X.convex hxm hx) h
  · grind only

end Derivative

section SuccMVF
open DyadicInterval Dyadic Vector MvPolynomial
variable {m n : ℕ}

/-- Successive mean-value form evaluation of `p` over the interval box `X`:
`f(Xm) + Σᵢ (∂f/∂xᵢ)(X.flatten i) · (Xᵢ − Xmᵢ)`, where each partial derivative `pderiv i p`
is evaluated naively (via `vectervalEvalWithPrec`) over the mixed box `X.flatten i` — the box
with coordinates `< i` collapsed to their midpoints and coordinate `i` (and beyond) left as
intervals. Compared to the naive `vectervalEvalWithPrec`, this curbs the dependency-problem
overestimation by replacing each variable's first occurrence with a degenerate midpoint. -/
def evalMvfWithPrec (prec : ℤ) (p : MvRatPol n) (X : Vecterval n) : DyadicInterval :=
  let const := p.evalWithPrec prec X.midpoint_rat
  let grad : Vecterval n :=
    Vecterval.ofFn (fun i => (pderiv i p).vectervalEvalWithPrec prec (Vecterval.flatten X i))
  let widths : Vecterval n := X - Vecterval.ofVecDyadic X.midpoint
  const + grad.dotProduct widths

/-- Telescoping mean-value identity underlying `evalMvfWithPrec`: for any point `x ∈ X` there
are witnesses `w i` in the mixed boxes `X.flatten i` realising the successive mean-value
expansion of `p` exactly. -/
theorem eval_mvf_eq (p : MvRatPol n) (X : Vecterval n) : ∀ x ∈ X, ∃ w : Fin n → (Fin n → ℝ),
  (∀ i : Fin n, w i ∈ (Vecterval.flatten X i).toSet) ∧
  (toMvRealPoly p).eval x.get = (toMvRealPoly p).eval X.midpoint_real.get
    + ∑ i, (toMvRealPoly (pderiv i p)).eval (w i) * (x.get i - X.midpoint_real.get i) := by
  intro x hx
  set m : Fin n → ℝ := X.midpoint_real.get with hm
  -- hybrid points: coordinates below `k` sit at the midpoint, the rest at `x`
  set z : ℕ → (Fin n → ℝ) := fun k j => if (j : ℕ) < k then m j else x.get j with hz
  -- every hybrid coordinate stays inside `X`
  have hzX : ∀ k (j : Fin n), z k j ∈ X.get j := by
    intro k j; simp only [hz]; split_ifs
    · exact X.midpoint_mem j
    · exact hx j
  -- a hybrid point with cut `≥ i` lies in the mixed box `flatten X i`
  have hmem : ∀ k (i : Fin n), (i : ℕ) ≤ k → z k ∈ (Vecterval.flatten X i).toSet := by
    intro k i hik
    rw [Vecterval.mem_toSet_iff, Vecterval.ofFn_mem_iff]
    intro j; rw [Vecterval.get_flatten]
    split_ifs with hji
    · have hji' : (j : ℕ) < (i : ℕ) := hji
      have hzkj : z k j = m j := by simp only [hz]; rw [if_pos (lt_of_lt_of_le hji' hik)]
      rw [hzkj, hm]
      simp only [Vecterval.midpoint_real, Vecterval.midpoint_rat, Vecterval.midpoint, Vector.get_map]
      exact to_rat_mem_of_dyadic _
    · exact hzX k j
  -- one-dimensional mean value step across coordinate `i`
  have step : ∀ i : Fin n, ∃ ξ, ξ ∈ (Vecterval.flatten X i).toSet ∧
      (toMvRealPoly p).eval (z i) - (toMvRealPoly p).eval (z ((i : ℕ) + 1))
        = (toMvRealPoly (pderiv i p)).eval ξ * (x.get i - m i) := by
    intro i
    have hconv := (Vecterval.flatten X i).convex
    have ha : z ((i : ℕ) + 1) ∈ (Vecterval.flatten X i).toSet := hmem _ i (Nat.le_succ _)
    have hb : z (i : ℕ) ∈ (Vecterval.flatten X i).toSet := hmem _ i (le_refl _)
    obtain ⟨ξ, hξ, hξ'⟩ :=
      domain_mvt (hasFDerivWithinAt_eval p (Vecterval.flatten X i)) hconv ha hb
    refine ⟨ξ, Set.mem_of_subset_of_mem (Convex.segment_subset hconv ha hb) hξ, ?_⟩
    rw [hξ']
    have hsingle : z (i : ℕ) - z ((i : ℕ) + 1) = Pi.single i (x.get i - m i) := by
      funext j; rw [Pi.sub_apply]; simp only [hz]
      rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
      · rw [if_pos (by omega), if_pos (by omega), sub_self,
          Pi.single_eq_of_ne (Fin.ne_of_val_ne (by omega))]
      · have hj : j = i := Fin.ext h
        subst hj
        rw [if_neg (by omega), if_pos (by omega), Pi.single_eq_same]
      · rw [if_neg (by omega), if_neg (by omega), sub_self,
          Pi.single_eq_of_ne (Fin.ne_of_val_ne (by omega))]
    rw [hsingle]
    simp only [MvRatPol.fderiv, map_sum, map_smul, ContinuousLinearMap.coe_sum',
      ContinuousLinearMap.coe_smul', LinearMap.coe_toContinuousLinearMap', LinearMap.coe_proj,
      Finset.sum_apply, Pi.smul_apply, Function.eval, Pi.single_apply, smul_eq_mul, mul_ite, MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  choose w hw hweq using step
  refine ⟨w, hw, ?_⟩
  have hz0 : z 0 = x.get := by funext j; simp only [hz]; rw [if_neg (Nat.not_lt_zero _)]
  have hzn : z n = m := by funext j; simp only [hz]; rw [if_pos j.2]
  have key : ∑ i : Fin n, (toMvRealPoly (pderiv i p)).eval (w i) * (x.get i - m i)
      = (toMvRealPoly p).eval x.get - (toMvRealPoly p).eval m := by
    have e1 : ∑ i : Fin n, (toMvRealPoly (pderiv i p)).eval (w i) * (x.get i - m i)
        = ∑ i : Fin n, ((toMvRealPoly p).eval (z i) - (toMvRealPoly p).eval (z ((i : ℕ) + 1))) :=
      Finset.sum_congr rfl (fun i _ => (hweq i).symm)
    rw [e1, Fin.sum_univ_eq_sum_range
        (fun k => (toMvRealPoly p).eval (z k) - (toMvRealPoly p).eval (z (k + 1))) n,
      Finset.sum_range_sub' (fun k => (toMvRealPoly p).eval (z k)) n, hz0, hzn]
  rw [key]; ring

/-- Soundness of the successive mean-value form: the true value of `p` at any point of the box `X` is contained in `evalMvfWithPrec prec p X`. -/
theorem eval_mvf_sound (prec : ℤ) (p : MvRatPol n) (X : Vecterval n) :
  ∀ x ∈ X, (toMvRealPoly p).eval x.get ∈ evalMvfWithPrec prec p X := by
  intro x hx
  obtain ⟨w, h₁, h₂⟩ := eval_mvf_eq p X x hx
  simp only [h₂, evalMvfWithPrec]
  apply add_sound
  · have h : X.midpoint_real.get = fun i ↦ ((X.midpoint_rat.get i : ℝ)) := by
      ext i; simp only [Vecterval.midpoint_real, Vector.get_map]
    rw [h]; exact eval_sound prec p X.midpoint_rat
  · simp only [Vecterval.dotProduct, dotProduct]
    apply Vecterval.sum_sound
    simp only [Finset.mem_univ, forall_const]
    simp only [Vecterval.get_ofFn, Vecterval.get_sub, Pi.sub_apply]
    intro i; specialize h₁ i
    apply mul_sound
    · have hm : Vector.ofFn (w i) ∈ Vecterval.flatten X i := by
        rw [← Vecterval.mem_toSet_iff]; exact h₁
      have := vecterval_eval_sound prec (pderiv i p) _ _ hm
      rw [← Vector.get_ofFn' (w i)] at this; exact this
    · apply sub_sound
      · exact hx i
      · simp only [Vecterval.ofVecDyadic, Vecterval.midpoint, Vecterval.midpoint_real,
          Vecterval.midpoint_rat, Vector.get_map]
        apply to_rat_mem_of_dyadic

end SuccMVF
end MvRatPol

/-- ℝ^k → ℝ^k -/
abbrev System (m n : ℕ) := Vector (MvRatPol n) m

namespace System
section MvRatPolynomialSystem
open DyadicInterval Dyadic Vector MvPolynomial MvRatPol
variable {m n : ℕ}

noncomputable abbrev toMv (S : System m n) := S.map (toMvPoly)
noncomputable abbrev toMvReal (S : System m n) := S.map (toMvRealPoly)

def X : System n n := Vector.ofFn (fun i ↦ MvRatPol.X i)

noncomputable def ratEval (S : System m n) (x : Vector ℚ n) : Vector ℝ m :=
  Vector.ofFn (fun i ↦ (toMvRealPoly (S.get i)).eval (fun i ↦ ↑(x.get i)))

noncomputable def eval (S : System m n) (x : Vector ℝ n) : Vector ℝ m :=
  Vector.ofFn (fun i ↦ (toMvRealPoly (S.get i)).eval x.get)

noncomputable def eval' (S : System m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ (toMvRealPoly (S.get i)).eval x

theorem eval_eq (S : System m n) (x : Vector ℝ n) : (S.eval x).get = (S.eval' x.get) := by
  grind only [eval, eval', get_ofFn]

theorem eval_X (x : Vector ℝ n) : eval X x = x := by
  ext i
  simp only [X, eval, getElem_ofFn, get_eq_getElem, to_mv_real_poly_X, MvPolynomial.eval_X]

def evalWithPrec (prec : ℤ) (S : System m n) (x : Vector ℚ n) : Vecterval m :=
  Vector.ofFn (fun i ↦ (S.get i).evalWithPrec prec x)

theorem rat_eval_sound (prec : ℤ) (S : System m n) (x : Vector ℚ n) :
  ratEval S x ∈ evalWithPrec prec S x := by
  grind only [ratEval, evalWithPrec, Vecterval.mem_iff, get_ofFn, eval_sound]

theorem eval_sound (prec : ℤ) (S : System m n) (x : Vector ℚ n) :
  eval S (x.map Rat.cast) ∈ evalWithPrec prec S x := by
  have : (Vector.map Rat.cast x).get = fun i ↦ ((x.get i) : ℝ) := by
    ext i; simp only [get_map]
  grind only [evalWithPrec, eval, Vecterval.mem_iff, get_ofFn, MvRatPol.eval_sound]

def vectervalEvalWithPrec (prec : ℤ) (S : System m n) (X : Vecterval n) : Vecterval m :=
  -- Vector.ofFn (fun i ↦ (S.get i).vectervalEvalWithPrec prec X)
  Vector.ofFn (fun i ↦ (S.get i).evalMvfWithPrec prec X)

theorem vecterval_eval_sound (prec : ℤ) (S : System m n) (X : Vecterval n) :
  ∀ x ∈ X, eval S x ∈ vectervalEvalWithPrec prec S X := by
  -- grind only [eval, vectervalEvalWithPrec, Vecterval.mem_iff, get_ofFn, vecterval_eval_sound]
  grind only [eval, vectervalEvalWithPrec, Vecterval.mem_iff, get_ofFn, eval_mvf_sound]

theorem mvt_real_sys (S : System m n) (X : Vecterval n) :
  ∀ x ∈ X, ∀ i, ∃ ξ ∈ X, (S.eval' x.get) i =
  (toMvRealPoly (S.get i)).eval X.midpoint_real.get +
  (fderiv (S.get i) ξ.get) (x.get - X.midpoint_real.get) := by
  intro x hx i
  exact mvt_real_poly (S.get i) X x hx

noncomputable def exactJacobian (S : System m n) (f : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j ↦ ((S.get i).fderiv f) (Pi.single j 1)

def jacobianEvalWithPrec (prec : ℤ) (S : System m n) (X : Vecterval n): Matrival m n :=
  let F : Fin m → Fin n → MvRatPol n := fun i j ↦ pderiv j (S.get i)
  -- Matrival.ofFn (fun i j ↦ (F i j).vectervalEvalWithPrec prec X)
  Matrival.ofFn (fun i j ↦ (F i j).evalMvfWithPrec prec X)

theorem jacobian_sound (prec : ℤ) (S : System m n) (X Y : Vecterval n) (x y : Vector ℝ n)
  (hx : x ∈ X) (hy : y ∈ Y) : ∀ i, (S.get i).fderiv x.get y.get ∈ ((jacobianEvalWithPrec prec S X) * Y).get i := by
  intro i
  change ((Vector.get S i).fderiv x.get) y.get ∈ Vector.get ((jacobianEvalWithPrec prec S X).mulVec Y) i
  simp only [MvRatPol.fderiv, map_sum, map_smul, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.coe_smul', LinearMap.coe_toContinuousLinearMap', LinearMap.coe_proj,
    Finset.sum_apply, Pi.smul_apply, Function.eval, smul_eq_mul]
  simp only [Matrival.mulVec, Matrix.mulVecᵣ, Matrix.dotProductᵣ_eq, dotProduct,
    jacobianEvalWithPrec, FinVec.map_eq, Vecterval.get_ofFn, Function.comp_apply]
  apply Vecterval.sum_sound
  simp only [Finset.mem_univ, forall_const]; intro j
  apply mul_sound
  · simp only [Matrival.get_ofFn]
    -- apply MvRatPol.vecterval_eval_sound
    apply MvRatPol.eval_mvf_sound
    exact hx
  · exact (hy j)

theorem exact_jacobian_sound (prec : ℤ) (S : System m n) (X : Vecterval n) :
  ∀ x ∈ X.toSet, exactJacobian S x ∈ jacobianEvalWithPrec prec S X := by
  intro x hx i j
  simp only [jacobianEvalWithPrec, Matrival.get_ofFn]
  simp only [exactJacobian, MvRatPol.fderiv, map_sum, map_smul, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.coe_smul', LinearMap.coe_toContinuousLinearMap', LinearMap.coe_proj,
    Finset.sum_apply, Pi.smul_apply, Function.eval, Pi.single_apply, smul_eq_mul, mul_ite,
    _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [Vecterval.mem_toSet_iff] at hx -- Vector.ofFn x ∈ X
  -- have h₁ := MvRatPol.vecterval_eval_sound prec (MvRatPol.pderiv j (Vector.get S i)) X _ hx
  have h₁ := MvRatPol.eval_mvf_sound prec (MvRatPol.pderiv j (Vector.get S i)) X _ hx
  have : (ofFn x).get = x := by ext i; simp only [Vector.get_ofFn]
  grind only

noncomputable def mixedJacobian (S : System m n) (ξ : Fin m → (Fin n → ℝ)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j ↦ ((S.get i).fderiv (ξ i)) (Pi.single j 1)

theorem mixedJacobian_sound (prec : ℤ) (S : System m n) (X : Vecterval n) (ξ : Fin m → (Fin n → ℝ))
  (h : ∀ i, ofFn (ξ i) ∈ X) : mixedJacobian S ξ ∈ jacobianEvalWithPrec prec S X := by
  unfold mixedJacobian; intro i j
  simp only [jacobianEvalWithPrec, Matrival.get_ofFn, MvRatPol.fderiv]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_proj, Finset.sum_apply, Pi.smul_apply,
    Function.eval, smul_eq_mul]
  simp only [Pi.single_apply, mul_ite, _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  -- have := MvRatPol.vecterval_eval_sound prec (MvRatPol.pderiv j (Vector.get S i)) X _ (h i)
  have := MvRatPol.eval_mvf_sound prec (MvRatPol.pderiv j (Vector.get S i)) X _ (h i)
  rw [Vector.get_ofFn' (ξ i)]
  -- exact MvRatPol.vecterval_eval_sound prec _ _ _ (h i)
  exact MvRatPol.eval_mvf_sound prec _ _ _ (h i)

lemma mixedJacobian_mulVec_eq (S : System m n) (ξ : Fin m → Fin n → ℝ)
  (v : Fin n → ℝ) (j : Fin m) :
  (mixedJacobian S ξ).mulVec v j = ((S.get j).fderiv (ξ j)) v := by
  unfold mixedJacobian; simp only [Matrix.mulVec]
  unfold _root_.dotProduct; simp only
  simp_rw [_root_.mul_comm, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1; ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.single_apply, mul_ite, _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

theorem mvt_real_sys' (S : System m n) (X : Vecterval n) : ∀ x ∈ X, ∃ ξ : Fin m → (Fin n → ℝ),
  (∀ i, ofFn (ξ i) ∈ X) ∧ S.eval' x.get = S.eval' (X.midpoint_real).get
  + (mixedJacobian S ξ).mulVec (x.get - (X.midpoint_real).get) := by
  intro x hx; --unfold mixedJacobian
  obtain h := mvt_real_sys S X x hx
  let Ξ := fun i : Fin m ↦ (Classical.choose (h i)).get
  have h' := fun i ↦ Classical.choose_spec (h i)
  use Ξ; simp only [Ξ]; constructor
  · intro j; simp only [Vector.ofFn_get]
    exact (h' j).1
  · ext j; rw[(h' j).2]
    unfold eval'
    simp only [Pi.add_apply, add_right_inj]
    simp only [mixedJacobian_mulVec_eq]

end MvRatPolynomialSystem
end System
