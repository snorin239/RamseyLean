import RamseyLean.Frontier
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Analytic core of the numerical optimization

This module contains the exact functions and calculus facts used in the two
numerical descent certificates for paper Theorem `t:main`.  The numerical
parameters below are independently chosen and need not agree with the
manuscript's Mathematica-assisted choices.
 -/

set_option autoImplicit false

namespace RamseyLean

open Set

noncomputable section

/-- The entropy term `h(r) = (1+r) log(1+r) - r log r`. -/
def entropy (r : ℝ) : ℝ :=
  (1 + r) * Real.log (1 + r) - r * Real.log r

/-- The polynomial multiplying `exp (-r)` in the correction term. -/
def gPoly (b r : ℝ) : ℝ :=
  -(1 / 4 : ℝ) * r + b * r ^ 2 + (2 / 25 : ℝ) * r ^ 3

/-- The correction term `g_b`. -/
def g (b r : ℝ) : ℝ :=
  gPoly b r * Real.exp (-r)

/-- The exponential rate `F_b = h + g_b`. -/
def F (b r : ℝ) : ℝ :=
  entropy r + g b r

/-- The explicit derivative of `F b`. -/
def FSlope (b r : ℝ) : ℝ :=
  Real.log (1 + r) - Real.log r + Real.exp (-r) *
    (-(1 / 4 : ℝ) + (2 * b + 1 / 4) * r +
      (6 / 25 - b) * r ^ 2 - (2 / 25) * r ^ 3)

/-- The polynomial factor in the second derivative of `F b`. -/
def curvaturePoly (b r : ℝ) : ℝ :=
  (1 / 2 : ℝ) + 2 * b + (23 / 100 - 4 * b) * r +
    (b - 12 / 25) * r ^ 2 + (2 / 25) * r ^ 3

/-- The explicit second derivative of `F b`. -/
def FCurvature (b r : ℝ) : ℝ :=
  -(1 / (r * (1 + r))) + Real.exp (-r) * curvaturePoly b r

/-- The coefficient used by the preliminary descent certificate. -/
def preliminaryB : ℝ := 3 / 40

/-- The coefficient in the final statement of paper Theorem `t:main`. -/
def finalB : ℝ := 3 / 100

/-- Short notation for the preliminary coefficient. -/
abbrev b₀ : ℝ := preliminaryB

/-- Short notation for the final coefficient. -/
abbrev b₁ : ℝ := finalB

/-- Independently chosen book parameter for the preliminary descent. -/
def preliminaryM (r : ℝ) : ℝ :=
  r * Real.exp (-(9 / 10 : ℝ) * r - (1 / 20 : ℝ) * r ^ 2)

/-- Independently chosen book parameter for the final descent. -/
def finalM (r : ℝ) : ℝ :=
  r * Real.exp (-(7 / 10 : ℝ) * r - (13 / 50 : ℝ) * r ^ 2)

/-- The positive base `1 - exp (-F_b')` in the descent choice of `X`. -/
def numericalP (b r : ℝ) : ℝ :=
  1 - Real.exp (-FSlope b r)

/-- The descent parameter determined by a coefficient `b` and book parameter
`M`, corresponding to equation `eq:X-def` in the paper. -/
def numericalX (b : ℝ) (M : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 - M r) * Real.rpow (numericalP b r) (1 / (1 - M r))

theorem hasDerivAt_entropy {r : ℝ} (hr : r ≠ 0) (h1r : 1 + r ≠ 0) :
    HasDerivAt entropy (Real.log (1 + r) - Real.log r) r := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 r :=
    (hasDerivAt_id r).const_add 1
  have h :=
    (h1.mul (h1.log h1r)).sub
      ((hasDerivAt_id r).mul ((hasDerivAt_id r).log hr))
  change HasDerivAt
    (fun x : ℝ => (1 + x) * Real.log (1 + x) - x * Real.log x)
    (Real.log (1 + r) - Real.log r) r
  exact h.congr_deriv (by
    simp only [id_eq]
    field_simp [hr, h1r] <;> ring)

theorem hasDerivAt_gPoly (b r : ℝ) :
    HasDerivAt (gPoly b)
      (-(1 / 4 : ℝ) + 2 * b * r + (6 / 25 : ℝ) * r ^ 2) r := by
  have h :=
    ((((hasDerivAt_const r (-(1 / 4 : ℝ))).mul (hasDerivAt_id r)).add
      ((hasDerivAt_const r b).mul ((hasDerivAt_id r).pow 2))).add
      ((hasDerivAt_const r (2 / 25 : ℝ)).mul ((hasDerivAt_id r).pow 3)))
  change HasDerivAt
    (fun x : ℝ => -(1 / 4 : ℝ) * x + b * x ^ 2 + (2 / 25 : ℝ) * x ^ 3)
    (-(1 / 4 : ℝ) + 2 * b * r + (6 / 25 : ℝ) * r ^ 2) r
  exact h.congr_deriv (by simp only [id_eq]; ring)

theorem hasDerivAt_g (b r : ℝ) :
    HasDerivAt (g b) (Real.exp (-r) *
      (-(1 / 4 : ℝ) + (2 * b + 1 / 4) * r +
        (6 / 25 - b) * r ^ 2 - (2 / 25) * r ^ 3)) r := by
  have h := (hasDerivAt_gPoly b r).mul ((hasDerivAt_id r).neg.exp)
  change HasDerivAt (fun x : ℝ => gPoly b x * Real.exp (-x)) _ r
  exact h.congr_deriv (by dsimp [gPoly]; ring)

/-- The displayed function `FSlope b` is the derivative of `F b` on the
positive half-line. -/
theorem hasDerivAt_F {b r : ℝ} (hr : 0 < r) :
    HasDerivAt (F b) (FSlope b r) r := by
  have h := (hasDerivAt_entropy hr.ne' (by linarith)).add (hasDerivAt_g b r)
  change HasDerivAt (fun x : ℝ => entropy x + g b x) (FSlope b r) r
  exact h.congr_deriv rfl

/-- The displayed function `FCurvature b` is the derivative of `FSlope b` on
the positive half-line. -/
theorem hasDerivAt_FSlope {b r : ℝ} (hr : 0 < r) :
    HasDerivAt (FSlope b) (FCurvature b r) r := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 r :=
    (hasDerivAt_id r).const_add 1
  have hlog1 := h1.log (by linarith : 1 + r ≠ 0)
  have hlogr := (hasDerivAt_id r).log hr.ne'
  let p : ℝ → ℝ := fun x =>
    -(1 / 4 : ℝ) + (2 * b + 1 / 4) * x +
      (6 / 25 - b) * x ^ 2 - (2 / 25) * x ^ 3
  have hp0 :=
    (((hasDerivAt_const r (-(1 / 4 : ℝ))).add
      ((hasDerivAt_const r (2 * b + 1 / 4)).mul (hasDerivAt_id r))).add
      ((hasDerivAt_const r (6 / 25 - b)).mul ((hasDerivAt_id r).pow 2))).sub
      ((hasDerivAt_const r (2 / 25 : ℝ)).mul ((hasDerivAt_id r).pow 3))
  have hp : HasDerivAt p
      ((2 * b + 1 / 4) + 2 * (6 / 25 - b) * r - (6 / 25) * r ^ 2) r := by
    change HasDerivAt
      (fun x : ℝ => -(1 / 4 : ℝ) + (2 * b + 1 / 4) * x +
        (6 / 25 - b) * x ^ 2 - (2 / 25) * x ^ 3) _ r
    exact hp0.congr_deriv (by simp only [id_eq]; ring)
  have h := (hlog1.sub hlogr).add (((hasDerivAt_id r).neg.exp).mul hp)
  change HasDerivAt
    (fun x : ℝ => Real.log (1 + x) - Real.log x + Real.exp (-x) *
      (-(1 / 4 : ℝ) + (2 * b + 1 / 4) * x +
        (6 / 25 - b) * x ^ 2 - (2 / 25) * x ^ 3))
    (-(1 / (r * (1 + r))) + Real.exp (-r) *
      ((1 / 2 : ℝ) + 2 * b + (23 / 100 - 4 * b) * r +
        (b - 12 / 25) * r ^ 2 + (2 / 25) * r ^ 3)) r
  exact h.congr_deriv (by
    dsimp [p]
    field_simp [hr.ne', (by linarith : 1 + r ≠ 0)] <;> ring)

theorem continuousOn_F (b : ℝ) : ContinuousOn (F b) (Ioc (0 : ℝ) 1) :=
  fun _ hr => (hasDerivAt_F hr.1).continuousAt.continuousWithinAt

theorem continuousOn_FSlope (b : ℝ) : ContinuousOn (FSlope b) (Ioc (0 : ℝ) 1) :=
  fun _ hr => (hasDerivAt_FSlope hr.1).continuousAt.continuousWithinAt

private theorem curvaturePoly_left_endpoint {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    curvaturePoly (3 / 100 : ℝ) r ≤ 33 / 50 := by
  have hr0 : 0 ≤ r := hr.1
  have hr1 : r ≤ 1 := hr.2
  have hcube : r ^ 3 ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr1)]
  have hsquare : 0 ≤ (r - (11 / 74 : ℝ)) ^ 2 := sq_nonneg _
  dsimp [curvaturePoly]
  nlinarith

private theorem curvaturePoly_right_endpoint {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    curvaturePoly (2 / 25 : ℝ) r ≤ 33 / 50 := by
  have hr0 : 0 ≤ r := hr.1
  have hr1 : r ≤ 1 := hr.2
  have hcube : r ^ 3 ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr1)]
  calc
    curvaturePoly (2 / 25 : ℝ) r =
        33 / 50 - (9 / 100 : ℝ) * r - (2 / 5 : ℝ) * r ^ 2 +
          (2 / 25 : ℝ) * r ^ 3 := by
      dsimp [curvaturePoly]
      ring
    _ ≤ 33 / 50 - (9 / 100 : ℝ) * r - (8 / 25 : ℝ) * r ^ 2 := by
      nlinarith
    _ ≤ 33 / 50 := by nlinarith [sq_nonneg r]

private theorem curvaturePoly_le {b r : ℝ}
    (hb : b ∈ Icc (3 / 100 : ℝ) (2 / 25)) (hr : r ∈ Icc (0 : ℝ) 1) :
    curvaturePoly b r ≤ 33 / 50 := by
  let w₀ : ℝ := 20 * (2 / 25 - b)
  let w₁ : ℝ := 20 * (b - 3 / 100)
  have hw₀ : 0 ≤ w₀ := by
    dsimp [w₀]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hb.2)
  have hw₁ : 0 ≤ w₁ := by
    dsimp [w₁]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hb.1)
  calc
    curvaturePoly b r = w₀ * curvaturePoly (3 / 100 : ℝ) r +
          w₁ * curvaturePoly (2 / 25 : ℝ) r := by
      dsimp [w₀, w₁, curvaturePoly]
      ring
    _ ≤ w₀ * (33 / 50 : ℝ) + w₁ * (33 / 50 : ℝ) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (curvaturePoly_left_endpoint hr) hw₀)
        (mul_le_mul_of_nonneg_left (curvaturePoly_right_endpoint hr) hw₁)
    _ = 33 / 50 := by dsimp [w₀, w₁]; ring

private theorem exp_neg_mul_one_add_le_one {r : ℝ} :
    Real.exp (-r) * (1 + r) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_inv_mul]
  exact (div_le_one (Real.exp_pos r)).2
    (by simpa [add_comm] using Real.add_one_le_exp r)

/-- The second derivative is strictly negative throughout the exact parameter
rectangle used by both numerical certificates. -/
theorem FCurvature_neg {b r : ℝ}
    (hb : b ∈ Icc finalB preliminaryB) (hr : r ∈ Ioc (0 : ℝ) 1) :
    FCurvature b r < 0 := by
  have hbwide : b ∈ Icc (3 / 100 : ℝ) (2 / 25) := by
    constructor
    · simpa [finalB] using hb.1
    · calc
        b ≤ preliminaryB := hb.2
        _ ≤ 2 / 25 := by norm_num [preliminaryB]
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r ≤ 1 := hr.2
  have hp := curvaturePoly_le hbwide ⟨hr0, hr1⟩
  have he := exp_neg_mul_one_add_le_one (r := r)
  have hfirst : Real.exp (-r) * curvaturePoly b r * r * (1 + r) ≤
      Real.exp (-r) * (33 / 50 : ℝ) * r * (1 + r) := by
    gcongr
  have hsecond : (33 / 50 : ℝ) * r * (Real.exp (-r) * (1 + r)) ≤
      (33 / 50 : ℝ) * r * 1 :=
    mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num) hr0)
  have hthird : (33 / 50 : ℝ) * r * 1 ≤ (33 / 50 : ℝ) * 1 := by
    simpa using mul_le_mul_of_nonneg_left hr1 (show (0 : ℝ) ≤ 33 / 50 by norm_num)
  have hprod : Real.exp (-r) * curvaturePoly b r * r * (1 + r) < 1 := by
    calc
      _ ≤ Real.exp (-r) * (33 / 50 : ℝ) * r * (1 + r) := hfirst
      _ = (33 / 50 : ℝ) * r * (Real.exp (-r) * (1 + r)) := by ring
      _ ≤ (33 / 50 : ℝ) * r * 1 := hsecond
      _ ≤ (33 / 50 : ℝ) * 1 := hthird
      _ < 1 := by norm_num
  have hden : 0 < r * (1 + r) := mul_pos hr.1 (by linarith)
  have hterm : Real.exp (-r) * curvaturePoly b r < 1 / (r * (1 + r)) := by
    apply (lt_div_iff₀ hden).2
    simpa [mul_assoc] using hprod
  dsimp [FCurvature]
  linarith

private def correctionSlopePoly (b r : ℝ) : ℝ :=
  -(1 / 4 : ℝ) + (2 * b + 1 / 4) * r +
    (6 / 25 - b) * r ^ 2 - (2 / 25) * r ^ 3

private theorem correctionSlopePoly_ge {b r : ℝ}
    (hb : b ∈ Icc (3 / 100 : ℝ) (2 / 25)) (hr : r ∈ Ioc (0 : ℝ) 1) :
    -(1 / 4 : ℝ) ≤ correctionSlopePoly b r := by
  have hr0 : 0 ≤ r := hr.1.le
  have hcube : r ^ 3 ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr.2)]
  have hc1 : 0 ≤ (2 * b + 1 / 4) * r := mul_nonneg (by nlinarith [hb.1]) hr0
  have hc2 : 0 ≤ (4 / 25 - b) * r ^ 2 :=
    mul_nonneg (by nlinarith [hb.2]) (sq_nonneg r)
  have hc3 : 0 ≤ (2 / 25 : ℝ) * (r ^ 2 - r ^ 3) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hcube)
  dsimp [correctionSlopePoly]
  nlinarith

private theorem log_two_le_entropySlope {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    Real.log 2 ≤ Real.log (1 + r) - Real.log r := by
  have hratio : (2 : ℝ) ≤ (1 + r) / r := by
    apply (le_div_iff₀ hr.1).2
    nlinarith [hr.2]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
  rw [Real.log_div (ne_of_gt (by linarith [hr.1] : 0 < 1 + r)) hr.1.ne'] at hlog
  exact hlog

private theorem correctionSlope_ge {b r : ℝ}
    (hb : b ∈ Icc (3 / 100 : ℝ) (2 / 25)) (hr : r ∈ Ioc (0 : ℝ) 1) :
    -(1 / 4 : ℝ) ≤ Real.exp (-r) * correctionSlopePoly b r := by
  have he : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hr.1])
  have hconst : -(1 / 4 : ℝ) ≤ Real.exp (-r) * (-(1 / 4 : ℝ)) := by
    have h := mul_le_mul_of_nonpos_right he (by norm_num : (-(1 / 4 : ℝ)) ≤ 0)
    nlinarith
  calc
    -(1 / 4 : ℝ) ≤ Real.exp (-r) * (-(1 / 4 : ℝ)) := hconst
    _ ≤ Real.exp (-r) * correctionSlopePoly b r :=
      mul_le_mul_of_nonneg_left (correctionSlopePoly_ge hb hr) (Real.exp_pos _).le

/-- `F_b'` is strictly positive throughout the exact parameter rectangle. -/
theorem FSlope_pos {b r : ℝ}
    (hb : b ∈ Icc finalB preliminaryB) (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < FSlope b r := by
  have hbwide : b ∈ Icc (3 / 100 : ℝ) (2 / 25) := by
    constructor
    · simpa [finalB] using hb.1
    · exact hb.2.trans (by norm_num [preliminaryB])
  have hlog := log_two_le_entropySlope hr
  have hcorr := correctionSlope_ge hbwide hr
  dsimp [FSlope, correctionSlopePoly] at *
  nlinarith [Real.log_two_gt_d9]

private theorem g_lower {b r : ℝ}
    (hb : b ∈ Icc (3 / 100 : ℝ) (2 / 25)) (hr : r ∈ Ioc (0 : ℝ) 1) :
    -(r / 4) ≤ g b r := by
  have hr0 : 0 ≤ r := hr.1.le
  have hb0 : 0 ≤ b := by nlinarith [hb.1]
  have hbr2 : 0 ≤ b * r ^ 2 := mul_nonneg hb0 (sq_nonneg r)
  have hcubic : 0 ≤ (2 / 25 : ℝ) * r ^ 3 := by positivity
  have hq : -(r / 4) ≤ gPoly b r := by
    dsimp [gPoly]
    nlinarith
  have he : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hr.1])
  have hconst : -(r / 4) ≤ Real.exp (-r) * (-(r / 4)) := by
    have hc : -(r / 4) ≤ 0 := by nlinarith
    have h := mul_le_mul_of_nonpos_right he hc
    nlinarith
  dsimp [g]
  calc
    -(r / 4) ≤ Real.exp (-r) * (-(r / 4)) := hconst
    _ ≤ Real.exp (-r) * gPoly b r :=
      mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    _ = gPoly b r * Real.exp (-r) := mul_comm _ _

private theorem entropy_gt_mul_log_two {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    r * Real.log 2 < entropy r := by
  have hlog := log_two_le_entropySlope hr
  have hmul := mul_le_mul_of_nonneg_left hlog hr.1.le
  have hpos : 0 < Real.log (1 + r) := Real.log_pos (by linarith [hr.1])
  dsimp [entropy]
  nlinarith

/-- `F_b` is strictly positive throughout the exact parameter rectangle. -/
theorem F_pos {b r : ℝ}
    (hb : b ∈ Icc finalB preliminaryB) (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < F b r := by
  have hbwide : b ∈ Icc (3 / 100 : ℝ) (2 / 25) := by
    constructor
    · simpa [finalB] using hb.1
    · exact hb.2.trans (by norm_num [preliminaryB])
  have hent := entropy_gt_mul_log_two hr
  have hg := g_lower hbwide hr
  have hlog : 0 < Real.log 2 - 1 / 4 := by nlinarith [Real.log_two_gt_d9]
  have hmul : 0 < r * (Real.log 2 - 1 / 4) := mul_pos hr.1 hlog
  dsimp [F]
  nlinarith

/-- The functions `F_b` used by both certificates are strictly concave on
`(0,1]`. -/
theorem strictConcaveOn_F {b : ℝ} (hb : b ∈ Icc finalB preliminaryB) :
    StrictConcaveOn ℝ (Ioc (0 : ℝ) 1) (F b) := by
  have hSlopeAnti : StrictAntiOn (FSlope b) (Ioc (0 : ℝ) 1) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioc (0 : ℝ) 1)
      (continuousOn_FSlope b)
    · intro r hr
      exact (hasDerivAt_FSlope (interior_subset hr).1).hasDerivWithinAt
    · intro r hr
      exact FCurvature_neg hb (interior_subset hr)
  have hDerivAnti : StrictAntiOn (deriv (F b)) (interior (Ioc (0 : ℝ) 1)) := by
    intro x hx y hy hxy
    rw [(hasDerivAt_F (interior_subset hx).1).deriv,
      (hasDerivAt_F (interior_subset hy).1).deriv]
    exact hSlopeAnti (interior_subset hx) (interior_subset hy) hxy
  exact hDerivAnti.strictConcaveOn_of_deriv
    (convex_Ioc (0 : ℝ) 1) (continuousOn_F b)

end

end RamseyLean
