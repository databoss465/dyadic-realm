import Mathlib
import DyadicRealm.DyadicIntervals.Basic
import DyadicRealm.DyadicIntervals.Arithmetic
import DyadicRealm.DyadicIntervals.Division
import DyadicRealm.DyadicIntervals.PolynomialBounds
import DyadicRealm.DyadicIntervals.PolynomialRoots
import DyadicRealm.DyadicIntervals.Vectervals

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

end Vector

-- List of Coeff, Monomial pairs; where monomial is represented by its power in each variable
-- ℝ^k → ℝ
abbrev MvRatPol (n : ℕ) := List (ℚ × Vector ℕ n)

-- ℝ^k → ℝ^k
abbrev System (m n : ℕ) := Vector (MvRatPol n) m

namespace MvRatPol
open DyadicInterval Dyadic Vector MvPolynomial
variable {m n : ℕ}

#check MvPolynomial.support_sum_monomial_coeff --Try not to use this!

-- Given a coefficeient a and multi-index; constructs a ⬝ x^i
noncomputable def toMvMono (q : ℚ × Vector ℕ n) : MvPolynomial (Fin n) ℚ :=
  -- Here Finset.univ = {0, 1,..., k-1}, because type is (Fin n)
  -- The third term is the proof, ∀ (i : Fin n), powers.get i ≠ 0 → i ∈ Finset.univ
  let f' := Finsupp.onFinset Finset.univ (q.2.get) (fun i _ => Finset.mem_univ i)
  monomial f' q.1   --f' is the Finite support version of powers.get

noncomputable def toMvRealMono (q : ℚ × Vector ℕ n) : MvPolynomial (Fin n) ℝ :=
  (toMvMono q).map (algebraMap ℚ ℝ)

noncomputable def toMvPoly (p : MvRatPol n) : MvPolynomial (Fin n) ℚ :=
  (p.map fun q ↦ toMvMono q).sum

noncomputable def toMvRealPoly (p : MvRatPol n) : MvPolynomial (Fin n) ℝ :=
  (toMvPoly p).map (algebraMap ℚ ℝ)

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

lemma to_mv_real_poly_trivial (p : MvRatPol n) : p = [] → toMvRealPoly p = 0 := by
  intro h; ext m
  simp only [coeff_zero, ← coeff_to_mv_real_poly]; norm_cast
  simp only [coeff, h, List.filter_nil, List.map_nil, List.sum_nil]


def pderivMono (i : Fin n) (coeff : ℚ) (powers : Vector ℕ n) : ℚ × Vector ℕ n :=
  let p := powers.get i
  if p = 0 then ⟨0, powers⟩
  else ⟨(coeff * p), powers.set i (p-1)⟩

def pderiv (i : Fin n) (p : MvRatPol n) : MvRatPol n := p.map (fun (a, xs) ↦ pderivMono i a xs)

def gradient (p : MvRatPol n) : System n n := ofFn (fun i ↦ pderiv i p)

def evalMonomial (q : ℚ × Vector ℕ n) (x : Vector ℚ n) : ℚ :=
  (zipWith (fun z n ↦ z^n) x q.2).foldr (· * ·) q.1

def evalWithPrec (prec : ℤ) (p : MvRatPol n) (x : Vector ℚ n) : DyadicInterval :=
  let rat_eval := (p.map (fun q ↦ evalMonomial q x)).sum
  ofRatWithPrec prec rat_eval

-- This must be foldr and not prod because we don't have CommMonoid DyadicInterval
def vectervalEvalMonomial (prec : ℤ) (q : ℚ × Vector ℕ n) (X : Vecterval n) :
  DyadicInterval :=
  let vs₀ := zip X q.2
  let vs : Vector DyadicInterval n := Vector.map (fun (z,n) ↦ z^n) vs₀
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

-- TODO : Successive Mean Value Form
#check add_sound
#check foldr
#check foldr_push
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

def jacobianEvalWithPrec (prec : ℤ) (S : System m n) (X : Vecterval n): Matrival m n :=
  let F : Fin m → Fin n → MvRatPol n := fun i j ↦ pderiv j (S.get i)
  Matrival.ofFn (fun i j ↦ vectervalEvalWithPrec prec (F i j) X)

end MvRatPol

open MvRatPol Matrival
def p₁ : MvRatPol 2 := [(2, #v[1, 0]), (1, #v[0,2])] -- 2x + y^2
def p₂ : MvRatPol 2 := [(1, #v[3, 0]), (1, #v[0,3])] -- x + y
def p₃ : MvRatPol 2 := [(3, #v[1,1])] -- 3xy
def S : System 3 2 := #v[p₁, p₂, p₃]
def J := jacobianEvalWithPrec 4 S X
def Y' := ApproxInvWithPrec J 4
#check Y' * J
