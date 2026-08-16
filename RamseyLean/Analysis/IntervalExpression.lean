import RamseyLean.Analysis.NormalizedFunctions
import Mathlib.Tactic

/-!
# Reflected interval expressions

This module implements a small, proof-producing interval evaluator for the
one-variable numerical certificates used in paper Lemma `lem:numerics`.
Expressions are ordinary inductive syntax, not an untrusted tactic: the theorem
`Expr.bound_sound` proves in Lean that every successful interval evaluation
contains the semantic value.

Besides arithmetic, positive reciprocals, exponentials, and logarithms, the
language has primitive nodes for the normalized removable quotients from
`NormalizedFunctions`.  Those nodes retain useful precision in cells touching
zero, where separately bounding a numerator and denominator would fail.
-/

set_option autoImplicit false

namespace RamseyLean.IntervalExpression

open Set
open CertifiedNumerics

noncomputable section

/-- A center-radius real interval.  Soundness is expressed by `Contains`; a
certificate never relies on computation outside Lean's kernel. -/
structure Interval where
  center : ℝ
  radius : ℝ

namespace Interval

/-- Lower endpoint of a center-radius interval. -/
def lower (I : Interval) : ℝ := I.center - I.radius

/-- Upper endpoint of a center-radius interval. -/
def upper (I : Interval) : ℝ := I.center + I.radius

/-- Membership in a center-radius interval. -/
def Contains (I : Interval) (x : ℝ) : Prop := |x - I.center| ≤ I.radius

/-- A degenerate interval. -/
def point (x : ℝ) : Interval := ⟨x, 0⟩

/-- The center-radius presentation of endpoint bounds. -/
def ofBounds (lo hi : ℝ) : Interval := ⟨(lo + hi) / 2, (hi - lo) / 2⟩

/-- Interval addition. -/
def add (I J : Interval) : Interval := ⟨I.center + J.center, I.radius + J.radius⟩

/-- Interval negation. -/
def neg (I : Interval) : Interval := ⟨-I.center, I.radius⟩

/-- Centered interval multiplication. -/
def mul (I J : Interval) : Interval :=
  ⟨I.center * J.center,
    |I.center| * J.radius + |J.center| * I.radius + I.radius * J.radius⟩

/-- Sharp endpoint multiplication for intervals known to be nonnegative. -/
def mulNonneg (I J : Interval) : Interval :=
  ofBounds (I.lower * J.lower) (I.upper * J.upper)

/-- Reciprocal of a positive interval.  Positivity is recorded by `Expr.Safe`. -/
def inv (I : Interval) : Interval := ofBounds (1 / I.upper) (1 / I.lower)

theorem contains_iff {I : Interval} {x : ℝ} :
    I.Contains x ↔ I.lower ≤ x ∧ x ≤ I.upper := by
  rw [Contains, abs_le]
  dsimp [lower, upper]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem contains_point (x : ℝ) : (point x).Contains x := by
  simp [Contains, point]

theorem contains_ofBounds {lo hi x : ℝ} (hx : lo ≤ x ∧ x ≤ hi) :
    (ofBounds lo hi).Contains x := by
  rw [contains_iff]
  dsimp [ofBounds, lower, upper]
  constructor <;> linarith

theorem Contains.radius_nonneg {I : Interval} {x : ℝ} (hx : I.Contains x) :
    0 ≤ I.radius := (abs_nonneg _).trans hx

theorem Contains.add {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  dsimp [Contains, add]
  calc
    |x + y - (I.center + J.center)| = |(x - I.center) + (y - J.center)| := by ring_nf
    _ ≤ |x - I.center| + |y - J.center| := abs_add_le _ _
    _ ≤ I.radius + J.radius := add_le_add hx hy

theorem Contains.neg {I : Interval} {x : ℝ} (hx : I.Contains x) :
    (neg I).Contains (-x) := by
  change |-x - (-I.center)| ≤ I.radius
  rw [show -x - -I.center = -(x - I.center) by ring, abs_neg]
  exact hx

theorem Contains.mul {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x * y) := by
  have hIr : 0 ≤ I.radius := hx.radius_nonneg
  have hJr : 0 ≤ J.radius := hy.radius_nonneg
  have h1 : |I.center| * |y - J.center| ≤ |I.center| * J.radius :=
    mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have h2 : |J.center| * |x - I.center| ≤ |J.center| * I.radius :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have h3 : |x - I.center| * |y - J.center| ≤ I.radius * J.radius :=
    mul_le_mul hx hy (abs_nonneg _) hIr
  dsimp [Contains, mul]
  calc
    |x * y - I.center * J.center| =
        |I.center * (y - J.center) + J.center * (x - I.center) +
          (x - I.center) * (y - J.center)| := by ring_nf
    _ ≤ |I.center * (y - J.center)| + |J.center * (x - I.center)| +
        |(x - I.center) * (y - J.center)| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |I.center| * |y - J.center| + |J.center| * |x - I.center| +
        (|x - I.center| * |y - J.center|) := by simp only [abs_mul]
    _ ≤ |I.center| * J.radius + |J.center| * I.radius + I.radius * J.radius :=
      add_le_add (add_le_add h1 h2) h3

theorem Contains.mulNonneg {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y)
    (hI : 0 ≤ I.lower) (hJ : 0 ≤ J.lower) :
    (mulNonneg I J).Contains (x * y) := by
  have hxBounds := contains_iff.mp hx
  have hyBounds := contains_iff.mp hy
  apply contains_ofBounds
  constructor
  · exact mul_le_mul hxBounds.1 hyBounds.1 hJ (hI.trans hxBounds.1)
  · exact mul_le_mul hxBounds.2 hyBounds.2 (hJ.trans hyBounds.1)
      ((hI.trans hxBounds.1).trans hxBounds.2)

theorem Contains.inv {I : Interval} {x : ℝ} (hx : I.Contains x)
    (hlo : 0 < I.lower) : (inv I).Contains x⁻¹ := by
  have hbounds := contains_iff.mp hx
  have hxpos : 0 < x := hlo.trans_le hbounds.1
  have huppos : 0 < I.upper := hxpos.trans_le hbounds.2
  apply contains_ofBounds
  constructor
  · simpa [one_div] using (inv_le_inv₀ huppos hxpos).2 hbounds.2
  · simpa [one_div] using (inv_le_inv₀ hxpos hlo).2 hbounds.1

end Interval

/-- One-variable expressions supported by the certified interval evaluator.
The natural number attached to an analytic node is its Taylor degree. -/
inductive Expr where
  | const (q : ℝ)
  | var
  | add (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | mulNonneg (a b : Expr)
  | inv (a : Expr)
  | exp (n : ℕ) (a : Expr)
  | log (n : ℕ) (a : Expr)
  | logOnePlusRatio (n : ℕ) (a : Expr)
  | negLogOneSubRatio (n : ℕ) (a : Expr)
  | oneSubExpNegRatio (n : ℕ) (a : Expr)

namespace Expr

/-- Real semantics of an interval expression. -/
def eval (x : ℝ) : Expr → ℝ
  | const q => q
  | var => x
  | add a b => eval x a + eval x b
  | neg a => -eval x a
  | mul a b => eval x a * eval x b
  | mulNonneg a b => eval x a * eval x b
  | inv a => (eval x a)⁻¹
  | exp _ a => Real.exp (eval x a)
  | log _ a => Real.log (eval x a)
  | logOnePlusRatio _ a => CertifiedNumerics.logOnePlusRatio (eval x a)
  | negLogOneSubRatio _ a => CertifiedNumerics.negLogOneSubRatio (eval x a)
  | oneSubExpNegRatio _ a => CertifiedNumerics.oneSubExpNegRatio (eval x a)

/-- Computed interval enclosure of an expression. -/
def bound (input : Interval) : Expr → Interval
  | const q => Interval.point q
  | var => input
  | add a b => Interval.add (bound input a) (bound input b)
  | neg a => Interval.neg (bound input a)
  | mul a b => Interval.mul (bound input a) (bound input b)
  | mulNonneg a b => Interval.mulNonneg (bound input a) (bound input b)
  | inv a => Interval.inv (bound input a)
  | exp n a =>
      let I := bound input a
      Interval.ofBounds (expPoly n I.lower - expError n I.lower)
        (expPoly n I.upper + expError n I.upper)
  | log n a =>
      let I := bound input a
      let za := (I.lower - 1) / (I.lower + 1)
      let zb := (I.upper - 1) / (I.upper + 1)
      Interval.ofBounds (2 * (logSeries n za - logError n za))
        (2 * (logSeries n zb + logError n zb))
  | logOnePlusRatio n a =>
      let I := bound input a
      Interval.ofBounds
        (CertifiedNumerics.logOnePlusRatioPolyLower n I.lower I.upper -
          CertifiedNumerics.logOnePlusRatioError n I.upper)
        (CertifiedNumerics.logOnePlusRatioPolyUpper n I.lower I.upper +
          CertifiedNumerics.logOnePlusRatioError n I.upper)
  | negLogOneSubRatio n a =>
      let I := bound input a
      Interval.ofBounds
        (CertifiedNumerics.negLogOneSubRatioPoly n I.lower -
          CertifiedNumerics.negLogOneSubRatioError n I.upper)
        (CertifiedNumerics.negLogOneSubRatioPoly n I.upper +
          CertifiedNumerics.negLogOneSubRatioError n I.upper)
  | oneSubExpNegRatio n a =>
      let I := bound input a
      Interval.ofBounds
        (CertifiedNumerics.oneSubExpNegRatioPolyLower n I.lower I.upper -
          CertifiedNumerics.oneSubExpNegRatioError n I.upper)
        (CertifiedNumerics.oneSubExpNegRatioPolyUpper n I.lower I.upper +
          CertifiedNumerics.oneSubExpNegRatioError n I.upper)

/-- Domain and Taylor-range side conditions for a successful evaluation. -/
def Safe (input : Interval) : Expr → Prop
  | const _ => True
  | var => True
  | add a b | mul a b => Safe input a ∧ Safe input b
  | mulNonneg a b => Safe input a ∧ Safe input b ∧
      0 ≤ (bound input a).lower ∧ 0 ≤ (bound input b).lower
  | neg a => Safe input a
  | inv a => Safe input a ∧ 0 < (bound input a).lower
  | exp n a => Safe input a ∧ 0 < n ∧
      |(bound input a).lower| ≤ 1 ∧ |(bound input a).upper| ≤ 1
  | log _ a => Safe input a ∧ 0 < (bound input a).lower
  | logOnePlusRatio n a | negLogOneSubRatio n a =>
      Safe input a ∧ 0 ≤ (bound input a).lower ∧
        (bound input a).upper < 1 ∧ 0 < n
  | oneSubExpNegRatio n a => Safe input a ∧ 0 ≤ (bound input a).lower ∧
      0 < n ∧ (bound input a).upper / (n + 2) ≤ 1 / 2

/-- Soundness of the reflected evaluator.  The conclusion is an ordinary Lean
proposition, so reducing a rational `Safe` goal with `norm_num` produces a
kernel-checked continuum certificate. -/
theorem bound_sound {input : Interval} {x : ℝ} (hx : input.Contains x) :
    ∀ e : Expr, Safe input e → (bound input e).Contains (eval x e) := by
  intro e
  induction e with
  | const q => intro _; exact Interval.contains_point q
  | var => intro _; exact hx
  | add a b iha ihb =>
      rintro ⟨ha, hb⟩
      exact (iha ha).add (ihb hb)
  | neg a ih =>
      intro ha
      exact (ih ha).neg
  | mul a b iha ihb =>
      rintro ⟨ha, hb⟩
      exact (iha ha).mul (ihb hb)
  | mulNonneg a b iha ihb =>
      rintro ⟨ha, hb, hloa, hlob⟩
      exact (iha ha).mulNonneg (ihb hb) hloa hlob
  | inv a ih =>
      rintro ⟨ha, hlo⟩
      exact (ih ha).inv hlo
  | exp n a ih =>
      rintro ⟨ha, hn, hblo, hbhi⟩
      have hv := ih ha
      have hvbounds := Interval.contains_iff.mp hv
      apply Interval.contains_ofBounds
      exact exp_on_interval hvbounds hblo hbhi hn le_rfl le_rfl
  | log n a ih =>
      rintro ⟨ha, hlo⟩
      have hv := ih ha
      have hvbounds := Interval.contains_iff.mp hv
      apply Interval.contains_ofBounds
      exact log_on_interval hvbounds hlo le_rfl le_rfl
  | logOnePlusRatio n a ih =>
      rintro ⟨ha, hlo, hhi, hn⟩
      have hv := ih ha
      apply Interval.contains_ofBounds
      exact CertifiedNumerics.logOnePlusRatio_on_interval
        (Interval.contains_iff.mp hv) hlo hhi hn
  | negLogOneSubRatio n a ih =>
      rintro ⟨ha, hlo, hhi, hn⟩
      have hv := ih ha
      apply Interval.contains_ofBounds
      exact CertifiedNumerics.negLogOneSubRatio_on_interval
        (Interval.contains_iff.mp hv) hlo hhi hn
  | oneSubExpNegRatio n a ih =>
      rintro ⟨ha, hlo, hn, hscale⟩
      have hv := ih ha
      apply Interval.contains_ofBounds
      exact CertifiedNumerics.oneSubExpNegRatio_on_interval
        (Interval.contains_iff.mp hv) hlo hn hscale

/-- Subtraction syntax. -/
def sub (a b : Expr) : Expr := add a (neg b)

/-- Division syntax; the denominator is certified positive by `Safe`. -/
def div (a b : Expr) : Expr := mul a (inv b)

/-- Natural powers, expanded using interval multiplication. -/
def pow (a : Expr) : ℕ → Expr
  | 0 => const 1
  | n + 1 => mul (pow a n) a

/-- Lower half of `bound_sound`, convenient for certificate theorems. -/
theorem lower_le_eval {input : Interval} {x : ℝ} (hx : input.Contains x)
    {e : Expr} (hsafe : Safe input e) : (bound input e).lower ≤ eval x e :=
  Interval.contains_iff.mp (bound_sound hx e hsafe) |>.1

/-- Upper half of `bound_sound`, convenient for certificate theorems. -/
theorem eval_le_upper {input : Interval} {x : ℝ} (hx : input.Contains x)
    {e : Expr} (hsafe : Safe input e) : eval x e ≤ (bound input e).upper :=
  Interval.contains_iff.mp (bound_sound hx e hsafe) |>.2

end Expr

end

end RamseyLean.IntervalExpression


