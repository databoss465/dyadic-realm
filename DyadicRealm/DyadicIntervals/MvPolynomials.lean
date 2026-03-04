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

lemma to_mv_poly_mono (q : ℚ × Vector ℕ n) : toMvPoly [q] = toMvMono q := by
  simp only [toMvPoly, toMvMono, List.map_singleton, List.sum_singleton]

noncomputable def toMvRealPoly (p : MvRatPol n) : MvPolynomial (Fin n) ℝ :=
  (toMvPoly p).map (algebraMap ℚ ℝ)

lemma to_mv_real_poly_mono (q : ℚ × Vector ℕ n) : toMvRealPoly [q] = toMvRealMono q := by
  simp only [toMvRealMono, toMvRealPoly]; congr 1
  simp only [to_mv_poly_mono]

def C (n : ℕ) (q : ℚ)  : MvRatPol n := [(q, 0)]

theorem to_mv_poly_C (n : ℕ) (q : ℚ) : toMvPoly (C n q) = MvPolynomial.C q := by
  simp only [C, to_mv_poly_mono, toMvMono]
  have : Finsupp.onFinset Finset.univ (Vector.get (0 : Vector ℕ n)) (fun i _ => Finset.mem_univ i) = 0 := by
    ext i; simp only [Finsupp.onFinset_apply, Finsupp.coe_zero, Pi.zero_apply]
    change Vector.get (replicate n 0) i = 0
    simp only [get_replicate]
  rw [this, ← MvPolynomial.C_apply]

theorem to_mv_real_poly_C (n : ℕ) (q : ℚ) : toMvRealPoly (C n q) = MvPolynomial.C ↑q := by
  simp only [toMvRealPoly, to_mv_poly_C, map_C, eq_ratCast]

def X (i : Fin n) : MvRatPol n := [(1, set 0 i 1)]

def X' : System n n := Vector.ofFn (fun i ↦ X i)

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

abbrev add (p q : MvRatPol n) := p ++ q
instance : Add (MvRatPol n) := ⟨add⟩

theorem toMvPoly_add (p q : MvRatPol n) :  toMvPoly (p + q) = toMvPoly p + toMvPoly q := by
  simp [toMvPoly, ← List.sum_append, ← List.map_append]; rfl

theorem cons_add (q : ℚ × Vector ℕ n)(qs : MvRatPol n) : q :: qs = [q] + qs := by rfl

theorem toMvRealPoly_add (p q : MvRatPol n) : toMvRealPoly (p + q) = toMvRealPoly p + toMvRealPoly q := by
  simp only [toMvRealPoly, toMvPoly_add, map_add]

def smul (r : ℚ) (p : MvRatPol n) : MvRatPol n := p.map (fun (q, v) ↦ (q * r, v))
instance : SMul ℚ (MvRatPol n) := ⟨smul⟩

theorem smul_add (r : ℚ) (p q : MvRatPol n) : r • (p + q) = r • p + r • q := by
  change (p ++ q).map (fun (q, v) ↦ (q * r, v)) = p.map (fun (q, v) ↦ (q * r, v)) ++ q.map (fun (q, v) ↦ (q * r, v))
  simp only [List.map_append]

theorem toMvRealPoly_smul (r : ℚ) (p : MvRatPol n) : toMvRealPoly (r • p) = r • toMvRealPoly p := by
  induction p with
  | nil =>
    change toMvRealPoly ([].map (fun (q, v) ↦ (q * r, v))) =  r • toMvRealPoly []
    simp [to_mv_real_poly_trivial]
  | cons q qs ih =>
    rw [cons_add, smul_add]
    simp only [toMvRealPoly_add, ih, _root_.smul_add, add_left_inj]
    change toMvRealPoly ([q].map (fun (q, v) ↦ (q * r, v))) =  r • toMvRealPoly [q]
    simp only [List.map_singleton, to_mv_real_poly_mono, toMvRealMono, toMvMono]
    simp only [map_monomial, eq_ratCast, Rat.cast_mul, smul_monomial, _root_.mul_comm]; congr

-- def neg (p : MvRatPol n) := (-1 : ℚ) • p
-- instance : Neg (MvRatPol n) := ⟨neg⟩

-- theorem toMvPoly_neg (p : MvRatPol n) : toMvPoly (-p) = - (toMvPoly p) := by
--   sorry

-- def sub (p q : MvRatPol n) := p + (-q)
-- instance : Sub (MvRatPol n) := ⟨sub⟩

-- theorem toMvPoly_sub (p q : MvRatPol n) :  toMvPoly (p - q) = toMvPoly p - toMvPoly q := by
--   sorry

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

-- TODO : Successive Mean Value Form

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

noncomputable def sysEval' (S : System m n) (x : Vector ℚ n) : Vector ℝ m :=
  Vector.ofFn (fun i ↦ (toMvRealPoly (S.get i)).eval (fun i ↦ ↑(x.get i)))

noncomputable def sysEval (S : System m n) (x : Vector ℝ n) : Vector ℝ m :=
  Vector.ofFn (fun i ↦ (toMvRealPoly (S.get i)).eval x.get)

theorem sys_eval_X (x : Vector ℝ n) : sysEval X' x = x := by
  ext i
  simp only [X', sysEval, getElem_ofFn, get_eq_getElem, to_mv_real_poly_X, eval_X]


def sysEvalWithPrec (prec : ℤ) (S : System m n) (x : Vector ℚ n) : Vecterval m :=
  Vector.ofFn (fun i ↦ evalWithPrec prec (S.get i) x)

theorem sys_eval_sound (prec : ℤ) (S : System m n) (x : Vector ℚ n) :
  sysEval' S x ∈ sysEvalWithPrec prec S x := by
  grind only [sysEval', sysEvalWithPrec, Vecterval.mem_iff, get_ofFn, eval_sound]

def sysVectervalEvalWithPrec (prec : ℤ) (S : System m n) (X : Vecterval n) : Vecterval m :=
  Vector.ofFn (fun i ↦ vectervalEvalWithPrec prec (S.get i) X)

theorem sys_vecterval_eval_sound (prec : ℤ) (S : System m n) (X : Vecterval n) :
  ∀ x ∈ X, sysEval S x ∈ sysVectervalEvalWithPrec prec S X := by
  grind only [sysEval, sysVectervalEvalWithPrec, Vecterval.mem_iff, get_ofFn, vecterval_eval_sound]

def pderivMono (i : Fin n) (coeff : ℚ) (powers : Vector ℕ n) : ℚ × Vector ℕ n :=
  let p := powers.get i
  if p = 0 then ⟨0, powers⟩
  else ⟨(coeff * p), powers.set i (p-1)⟩

def pderiv (i : Fin n) (p : MvRatPol n) : MvRatPol n := p.map (fun (a, xs) ↦ pderivMono i a xs)

lemma pderiv_cons (i : Fin n) (q : ℚ × Vector ℕ n)(qs : MvRatPol n) :
  pderiv i (q :: qs) = pderiv i [q] + pderiv i qs := by
  simp only [pderiv, List.map_cons, List.map_nil]; rfl

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

def gradient (p : MvRatPol n) : System n n := ofFn (fun i ↦ pderiv i p)

noncomputable def fderiv (p : MvRatPol n) (f : Fin n → ℝ) : StrongDual ℝ ((Fin n) → ℝ) :=
  let grad_eval (i : Fin n) : ℝ := (toMvRealPoly (pderiv i p)).eval f
  LinearMap.toContinuousLinearMap (∑ i : Fin n, grad_eval i • LinearMap.proj i)

theorem fderiv_trivial (x : Fin n → ℝ) : fderiv [] x = 0 := by
  simp only [fderiv, pderiv, List.map_nil, to_mv_real_poly_trivial,
    _root_.zero_smul, Finset.sum_const_zero, map_zero]

theorem fderiv_cons (x : Fin n → ℝ) (q : ℚ × Vector ℕ n)(qs : MvRatPol n) :
  fderiv (q :: qs) x = fderiv [q] x + fderiv qs x := by
  simp only [fderiv, map_sum, map_smul, ← Finset.sum_add_distrib]; congr 1
  ext i v; rw [pderiv_cons]
  simp only [toMvRealPoly_add, eval_add, ContinuousLinearMap.coe_smul',
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

def jacobianEvalWithPrec (prec : ℤ) (S : System m n) (X : Vecterval n): Matrival m n :=
  let F : Fin m → Fin n → MvRatPol n := fun i j ↦ pderiv j (S.get i)
  Matrival.ofFn (fun i j ↦ vectervalEvalWithPrec prec (F i j) X)

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

end MvRatPol

-- open MvRatPol Matrival
-- def p₁ : MvRatPol 2 := [(2, #v[1, 0]), (1, #v[0,2])] -- 2x + y^2
-- def p₂ : MvRatPol 2 := [(1, #v[3, 0]), (1, #v[0,3])] -- x + y
-- def p₃ : MvRatPol 2 := [(3, #v[1,1])] -- 3xy
-- def S : System 3 2 := #v[p₁, p₂, p₃]
-- def J := jacobianEvalWithPrec 4 S X
-- def Y' := ApproxInvWithPrec J 4
-- #check Y' * J
