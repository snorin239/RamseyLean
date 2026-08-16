import RamseyLean.Numerics.Preliminary
import RamseyLean.Numerics.FrontierFacts
import RamseyLean.Analysis.IntervalMesh

/-!
# Final numerical descent certificate

This module implements the second numerical descent used for paper Theorem
`t:main`.  The independently selected parameters are
`b₁ = 3 / 100` and
`M₁(r) = r * exp (-(7 / 10) r - (13 / 50) r²)`.

The analytic definitions below expose the removable factor in `log X₁`.  The
remaining continuum inequalities are certified on one-variable rational
meshes, using approximate points on the already-proved preliminary frontier.
-/

set_option autoImplicit false

namespace RamseyLean

open Set

noncomputable section

/-- The polynomial remainder in the factored final slope. -/
def finalRemainder (r : ℝ) : ℝ :=
  -(1 / 4 : ℝ) + (31 / 100 : ℝ) * r + (21 / 100 : ℝ) * r ^ 2 -
    (2 / 25 : ℝ) * r ^ 3

/-- The quantity `exp (-F'_{b₁}(r))`, with its factor `r` exposed. -/
def finalA (r : ℝ) : ℝ :=
  r / (1 + r) * Real.exp (-Real.exp (-r) * finalRemainder r)

/-- The `X` parameter in the final descent. -/
def finalX (r : ℝ) : ℝ := numericalX finalB finalM r

/-- The factor `M₁(r) / r`, extended smoothly to zero. -/
def finalMRatio (r : ℝ) : ℝ :=
  Real.exp (-(7 / 10 : ℝ) * r - (13 / 50 : ℝ) * r ^ 2)

/-- The factor `exp (-F'_{b₁}(r)) / r`, extended smoothly to zero. -/
def finalARatio (r : ℝ) : ℝ :=
  Real.exp (-Real.exp (-r) * finalRemainder r) / (1 + r)

/-- The smooth factor `-log X₁(r) / r`. -/
def finalU (r : ℝ) : ℝ :=
  finalMRatio r * CertifiedNumerics.negLogOneSubRatio (finalM r) +
    finalARatio r * CertifiedNumerics.negLogOneSubRatio (finalA r) /
      (1 - finalM r)

/-- Positive slack for a proposed second coordinate `y`. -/
def finalSlack (r y : ℝ) : ℝ :=
  F finalB r +
    (Real.log (finalX r) + r * Real.log (finalM r) + r * Real.log y) / 2

/-- Final slack divided by `r`, with the selected coordinate left explicit. -/
def finalNormalizedSlack (r y : ℝ) : ℝ :=
  (1 + r) * (Real.log (1 + r) / r) +
    Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
      (2 / 25 : ℝ) * r ^ 2) -
    finalU r / 2 - (7 / 20 : ℝ) * r - (13 / 100 : ℝ) * r ^ 2 -
    Real.log r / 2 + Real.log y / 2

theorem exp_neg_FSlope_final {r : ℝ} (hr : 0 < r) :
    Real.exp (-FSlope finalB r) = finalA r := by
  have h1r : 0 < 1 + r := by linarith
  have hexponent :
      -FSlope finalB r =
        (Real.log r - Real.log (1 + r)) +
          (-Real.exp (-r) * finalRemainder r) := by
    simp only [FSlope, finalB, finalRemainder]
    ring
  rw [hexponent, Real.exp_add, Real.exp_sub, Real.exp_log hr,
    Real.exp_log h1r]
  rfl

theorem numericalP_final_eq {r : ℝ} (hr : 0 < r) :
    numericalP finalB r = 1 - finalA r := by
  rw [numericalP, exp_neg_FSlope_final hr]

theorem finalM_eq_mul_ratio (r : ℝ) :
    finalM r = r * finalMRatio r := rfl

theorem finalA_eq_mul_ratio {r : ℝ} (hr : 0 < r) :
    finalA r = r * finalARatio r := by
  dsimp [finalA, finalARatio]
  field_simp [hr.ne', (by linarith : 1 + r ≠ 0)]

theorem finalX_mem_Ioo {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    finalX r ∈ Ioo (0 : ℝ) 1 := by
  exact numericalX_mem_Ioo
    ⟨le_rfl, by norm_num [finalB, preliminaryB]⟩ hr (finalM_mem_Ioo hr)

theorem finalX_eq_descent (r : ℝ) :
    finalX r =
      (1 - Real.exp (-FSlope finalB r)) ^ (1 / (1 - finalM r)) *
        (1 - finalM r) := by
  simpa [finalX] using
    (numericalX_eq_descent (b := finalB) (r := r) (M := finalM))

theorem log_finalX {r : ℝ}
    (hM : finalM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP finalB r ∈ Ioo (0 : ℝ) 1) :
    Real.log (finalX r) = Real.log (1 - finalM r) +
      Real.log (numericalP finalB r) / (1 - finalM r) := by
  have hOneM : 0 < 1 - finalM r := sub_pos.mpr hM.2
  have hpow : 0 < Real.rpow (numericalP finalB r)
      (1 / (1 - finalM r)) := Real.rpow_pos_of_pos hP.1 _
  have hlogpow :
      Real.log (Real.rpow (numericalP finalB r)
        (1 / (1 - finalM r))) =
          (1 / (1 - finalM r)) * Real.log (numericalP finalB r) := by
    simpa only [Real.rpow_eq_pow] using
      Real.log_rpow hP.1 (1 / (1 - finalM r))
  calc
    Real.log (finalX r) = Real.log (1 - finalM r) +
        Real.log (Real.rpow (numericalP finalB r)
          (1 / (1 - finalM r))) := by
      rw [finalX, numericalX, Real.log_mul hOneM.ne' hpow.ne']
    _ = Real.log (1 - finalM r) +
        (1 / (1 - finalM r)) * Real.log (numericalP finalB r) := by
      rw [hlogpow]
    _ = Real.log (1 - finalM r) +
        Real.log (numericalP finalB r) / (1 - finalM r) := by ring

theorem finalU_eq_neg_log_div {r : ℝ} (hr : 0 < r)
    (hM : finalM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP finalB r ∈ Ioo (0 : ℝ) 1) :
    finalU r = -Real.log (finalX r) / r := by
  rw [log_finalX hM hP, numericalP_final_eq hr]
  have hmR : 0 < finalMRatio r := Real.exp_pos _
  have haR : 0 < finalARatio r :=
    div_pos (Real.exp_pos _) (by linarith)
  have hMne : r * finalMRatio r ≠ 0 := mul_ne_zero hr.ne' hmR.ne'
  have hAne : r * finalARatio r ≠ 0 := mul_ne_zero hr.ne' haR.ne'
  have hden : 1 - r * finalMRatio r ≠ 0 := by
    rw [← finalM_eq_mul_ratio r]
    linarith [hM.2]
  simp only [finalU, finalM_eq_mul_ratio r, finalA_eq_mul_ratio hr]
  rw [CertifiedNumerics.negLogOneSubRatio_eq_of_ne hMne,
    CertifiedNumerics.negLogOneSubRatio_eq_of_ne hAne]
  field_simp [hr.ne', hmR.ne', haR.ne', hden]
  ring

theorem log_finalM {r : ℝ} (hr : 0 < r) :
    Real.log (finalM r) = Real.log r - (7 / 10 : ℝ) * r -
      (13 / 50 : ℝ) * r ^ 2 := by
  have hmR : 0 < finalMRatio r := Real.exp_pos _
  rw [finalM_eq_mul_ratio r, Real.log_mul hr.ne' hmR.ne']
  dsimp [finalMRatio]
  rw [Real.log_exp]
  ring

/-- Exact bridge from the final slack to its normalized form. -/
theorem finalSlack_eq_mul_normalized {r y : ℝ} (hr : 0 < r)
    (hM : finalM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP finalB r ∈ Ioo (0 : ℝ) 1) :
    finalSlack r y = r * finalNormalizedSlack r y := by
  have hU := finalU_eq_neg_log_div hr hM hP
  have hlogX : Real.log (finalX r) = -(r * finalU r) := by
    rw [hU]
    field_simp [hr.ne']
  rw [finalSlack, hlogX, log_finalM hr]
  dsimp [finalNormalizedSlack, F, entropy, g, gPoly, finalB]
  field_simp [hr.ne']
  ring

theorem denseCaseExponent_final_eq (r y : ℝ) :
    denseCaseExponent (finalX r) (finalM r) y r =
      F finalB r - finalSlack r y := by
  dsimp [denseCaseExponent, finalSlack]
  ring


/-! ## Explicit approximate-frontier selection -/

/-- Horner evaluation of a rational quartic. -/
def finalQuartic (c₀ c₁ c₂ c₃ c₄ u : ℝ) : ℝ :=
  c₀ + u * (c₁ + u * (c₂ + u * (c₃ + u * c₄)))

/-- The quartic factor t/r on the small-r frontier branch. -/
def finalSmallRatio (r : ℝ) : ℝ :=
  if r ≤ 1 / 10 then
    let u := 10 * r
    finalQuartic (22764 / 10000) (4213 / 10000) (823 / 10000)
      (213 / 10000) (-(41 / 10000)) u
  else if r ≤ 1 / 5 then
    let u := 10 * r - 1
    finalQuartic (27971 / 10000) (6328 / 10000) (1148 / 10000)
      (29 / 10000) (-(385 / 10000)) u
  else
    let u := (50 / 3) * (r - 1 / 5)
    finalQuartic (35092 / 10000) (4307 / 10000) (-(348 / 10000))
      (-(305 / 10000)) (65 / 10000) u

/-- Approximate parameter for the small-r, B-coordinate frontier branch. -/
def finalSmallParameter (r : ℝ) : ℝ := r * finalSmallRatio r

/-- Approximate parameter for the large-r, A-coordinate frontier branch. -/
def finalLargeParameter (r : ℝ) : ℝ :=
  if r ≤ 9 / 20 then
    let u := (100 / 9) * (r - 9 / 25)
    finalQuartic (10036 / 10000) (-(4315 / 10000)) (1157 / 10000)
      (-(101 / 10000)) (-(23 / 10000)) u
  else if r ≤ 3 / 5 then
    let u := (20 / 3) * (r - 9 / 20)
    finalQuartic (6755 / 10000) (-(3986 / 10000)) (2018 / 10000)
      (-(717 / 10000)) (136 / 10000) u
  else
    let u := (5 / 2) * (r - 3 / 5)
    finalQuartic (4206 / 10000) (-(4085 / 10000)) (4170 / 10000)
      (-(2475 / 10000)) (702 / 10000) u

/-- The exact hyperbolic coordinate used on the middle branch. -/
def finalMiddleY (r : ℝ) : ℝ :=
  Real.exp (-F preliminaryB 1) / finalX r

/-- The explicit second coordinate used by the final descent.  Comparisons
with the two t=1 frontier coordinates place the two irrational crossings
exactly, without pretending that either crossing is rational. -/
def finalY (r : ℝ) : ℝ :=
  if frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r then
    frontierA (FSlope preliminaryB) (finalSmallParameter r)
  else if frontierA (FSlope preliminaryB) 1 ≤ finalX r then
    finalMiddleY r
  else if r ≤ 361 / 1000 then
    frontierB (F preliminaryB) (FSlope preliminaryB) 1
  else
    frontierB (F preliminaryB) (FSlope preliminaryB) (finalLargeParameter r)


/-- Smooth normalized slack on the small-r outer branch.  The logarithms of r
cancel after writing the frontier parameter as r times finalSmallRatio. -/
def finalSmallNormalizedSlack (r : ℝ) : ℝ :=
  (1 + r) * CertifiedNumerics.logOnePlusRatio r +
    Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
      (2 / 25 : ℝ) * r ^ 2) -
    finalU r / 2 - (7 / 20 : ℝ) * r - (13 / 100 : ℝ) * r ^ 2 +
    (Real.log (finalSmallRatio r) -
      Real.log (1 + finalSmallParameter r) -
      Real.exp (-finalSmallParameter r) *
        preliminaryFrontierR (finalSmallParameter r)) / 2

/-- Simplified normalized slack on the hyperbolic middle branch. -/
def finalMiddleNormalizedSlack (r : ℝ) : ℝ :=
  (1 + r) * (Real.log (1 + r) / r) +
    Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
      (2 / 25 : ℝ) * r ^ 2) -
    (1 - r) * finalU r / 2 - (7 / 20 : ℝ) * r -
    (13 / 100 : ℝ) * r ^ 2 - Real.log r / 2 -
    F preliminaryB 1 / 2

/-- Simplified normalized slack on the short t=1 cap immediately after
the irrational A-coordinate crossing. -/
def finalLargeCapNormalizedSlack (r : ℝ) : ℝ :=
  (1 + r) * (Real.log (1 + r) / r) +
    Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
      (2 / 25 : ℝ) * r ^ 2) -
    finalU r / 2 - (7 / 20 : ℝ) * r - (13 / 100 : ℝ) * r ^ 2 -
    Real.log r / 2 +
    (-Real.log (1 + (1 : ℝ)) +
      Real.exp (-(1 : ℝ)) * preliminaryFrontierS 1) / 2

/-- Simplified normalized slack on the large-r outer branch. -/
def finalLargeNormalizedSlack (r : ℝ) : ℝ :=
  (1 + r) * (Real.log (1 + r) / r) +
    Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
      (2 / 25 : ℝ) * r ^ 2) -
    finalU r / 2 - (7 / 20 : ℝ) * r - (13 / 100 : ℝ) * r ^ 2 -
    Real.log r / 2 +
    (-Real.log (1 + finalLargeParameter r) +
      Real.exp (-finalLargeParameter r) *
        preliminaryFrontierS (finalLargeParameter r)) / 2

/-- Exact smooth bridge for the small-r outer branch. -/
theorem finalSlack_small_eq_mul_normalized {r : ℝ} (hr : 0 < r)
    (hM : finalM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP finalB r ∈ Ioo (0 : ℝ) 1)
    (hp : 0 < finalSmallRatio r) :
    finalSlack r
        (frontierA (FSlope preliminaryB) (finalSmallParameter r)) =
      r * finalSmallNormalizedSlack r := by
  rw [finalSlack_eq_mul_normalized hr hM hP]
  congr 1
  unfold finalNormalizedSlack finalSmallNormalizedSlack
  rw [CertifiedNumerics.logOnePlusRatio_eq_of_ne hr.ne',
    log_frontierA_preliminary, finalSmallParameter,
    Real.log_mul hr.ne' hp.ne']
  ring

/-- Logarithm of the exact hyperbolic middle coordinate. -/
theorem log_finalMiddleY {r : ℝ} (hX : 0 < finalX r) :
    Real.log (finalMiddleY r) =
      -F preliminaryB 1 - Real.log (finalX r) := by
  unfold finalMiddleY
  rw [Real.log_div (Real.exp_ne_zero _) hX.ne', Real.log_exp]

/-- Exact smooth bridge for the hyperbolic middle branch. -/
theorem finalSlack_middle_eq_mul_normalized {r : ℝ} (hr : 0 < r)
    (hM : finalM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP finalB r ∈ Ioo (0 : ℝ) 1) :
    finalSlack r (finalMiddleY r) =
      r * finalMiddleNormalizedSlack r := by
  have hOneM : 0 < 1 - finalM r := sub_pos.mpr hM.2
  have hpow : 0 < Real.rpow (numericalP finalB r)
      (1 / (1 - finalM r)) := Real.rpow_pos_of_pos hP.1 _
  have hX : 0 < finalX r := by
    unfold finalX numericalX
    exact mul_pos hOneM hpow
  have hlogX : Real.log (finalX r) = -(r * finalU r) := by
    rw [finalU_eq_neg_log_div hr hM hP]
    field_simp [hr.ne']
  rw [finalSlack_eq_mul_normalized hr hM hP]
  congr 1
  unfold finalNormalizedSlack finalMiddleNormalizedSlack
  rw [log_finalMiddleY hX, hlogX]
  ring

/-- Exact smooth bridge for the short t=1 large-branch cap. -/
theorem finalSlack_largeCap_eq_mul_normalized {r : ℝ} (hr : 0 < r)
    (hM : finalM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP finalB r ∈ Ioo (0 : ℝ) 1) :
    finalSlack r
        (frontierB (F preliminaryB) (FSlope preliminaryB) 1) =
      r * finalLargeCapNormalizedSlack r := by
  rw [finalSlack_eq_mul_normalized hr hM hP]
  congr 1
  unfold finalNormalizedSlack finalLargeCapNormalizedSlack
  rw [log_frontierB_preliminary]

/-- Exact smooth bridge for the large-r outer branch. -/
theorem finalSlack_large_eq_mul_normalized {r : ℝ} (hr : 0 < r)
    (hM : finalM r ∈ Ioo (0 : ℝ) 1)
    (hP : numericalP finalB r ∈ Ioo (0 : ℝ) 1) :
    finalSlack r
        (frontierB (F preliminaryB) (FSlope preliminaryB)
          (finalLargeParameter r)) =
      r * finalLargeNormalizedSlack r := by
  rw [finalSlack_eq_mul_normalized hr hM hP]
  congr 1
  unfold finalNormalizedSlack finalLargeNormalizedSlack
  rw [log_frontierB_preliminary]

/-- Named numerical obligations for the approximate-frontier construction.
Every field is a one-variable inequality intended to be discharged by the
kernel-checked interval backend. -/
structure FinalRegionCertificate : Prop where
  small_parameter_mem :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r →
      finalSmallParameter r ∈ Ioc (0 : ℝ) 1
  small_coordinate :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r →
      finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB)
        (finalSmallParameter r)
  large_parameter_mem :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      (361 / 1000 : ℝ) < r →
      finalX r < frontierA (FSlope preliminaryB) 1 →
      finalLargeParameter r ∈ Ioc (0 : ℝ) 1
  large_coordinate :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      (361 / 1000 : ℝ) < r →
      finalX r < frontierA (FSlope preliminaryB) 1 →
      finalX r ≤ frontierA (FSlope preliminaryB) (finalLargeParameter r)

/-- The branchwise frontier construction produces a valid second coordinate
throughout the final descent interval. -/
theorem finalY_mem_asymptoticRegion
    (hF : UniformRamseyExpBound (F preliminaryB))
    (hcert : FinalRegionCertificate)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    finalY r ∈ Ioo (0 : ℝ) 1 ∧
      (finalX r, finalY r) ∈ asymptoticRegion := by
  classical
  have hX := finalX_mem_Ioo hr
  by_cases hsmall :
      frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r
  · have ht := hcert.small_parameter_mem hr hsmall
    have hcoord := hcert.small_coordinate hr hsmall
    have hp := preliminary_frontier_pair_mem hF ht
    rw [finalY, if_pos hsmall]
    refine ⟨hp.1, ?_⟩
    exact AsymptoticRegion.lower hp.2.2.2 hX.1 hcoord hp.1.1 le_rfl
  · have hXB :
      finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB) 1 :=
        le_of_not_gt hsmall
    by_cases hmiddle : frontierA (FSlope preliminaryB) 1 ≤ finalX r
    · have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := by constructor <;> norm_num
      have hp := preliminary_frontier_pair_mem hF hone
      have hb : preliminaryB ∈ Icc finalB preliminaryB :=
        ⟨by norm_num [finalB, preliminaryB], le_rfl⟩
      have hm := frontier_middle_mem_asymptoticRegion hF
        (strictConcaveOn_F hb).concaveOn
        (hasDerivAt_F (b := preliminaryB) (by norm_num))
        hp.1 hp.2.1 ⟨hmiddle, hXB⟩
      rw [finalY, if_neg hsmall, if_pos hmiddle]
      exact hm
    · have hlarge :
        finalX r < frontierA (FSlope preliminaryB) 1 := lt_of_not_ge hmiddle
      by_cases hcap : r ≤ (361 / 1000 : ℝ)
      · have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := by
          constructor <;> norm_num
        have hp := preliminary_frontier_pair_mem hF hone
        rw [finalY, if_neg hsmall, if_neg hmiddle, if_pos hcap]
        refine ⟨hp.2.1, ?_⟩
        exact AsymptoticRegion.lower hp.2.2.1 hX.1 hlarge.le
          hp.2.1.1 le_rfl
      · have hcut : (361 / 1000 : ℝ) < r := lt_of_not_ge hcap
        have ht := hcert.large_parameter_mem hr hcut hlarge
        have hcoord := hcert.large_coordinate hr hcut hlarge
        have hp := preliminary_frontier_pair_mem hF ht
        rw [finalY, if_neg hsmall, if_neg hmiddle, if_neg hcap]
        refine ⟨hp.2.1, ?_⟩
        exact AsymptoticRegion.lower hp.2.2.1 hX.1 hcoord
          hp.2.1.1 le_rfl

/-- The remaining scalar numerical obligations.  Each branch is a smooth
one-variable positivity inequality, with the exact frontier comparisons
retained as hypotheses so that the two irrational crossing points need not be
rounded. -/
structure FinalNumericalCertificate : Prop extends FinalRegionCertificate where
  small_slack_pos :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r →
      0 < finalSmallNormalizedSlack r
  middle_slack_pos :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      ¬frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r →
      frontierA (FSlope preliminaryB) 1 ≤ finalX r →
      0 < finalMiddleNormalizedSlack r
  large_cap_slack_pos :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      finalX r < frontierA (FSlope preliminaryB) 1 →
      r ≤ (361 / 1000 : ℝ) →
      0 < finalLargeCapNormalizedSlack r
  large_slack_pos :
    ∀ {r : ℝ}, r ∈ Ioc (0 : ℝ) 1 →
      (361 / 1000 : ℝ) < r →
      finalX r < frontierA (FSlope preliminaryB) 1 →
      0 < finalLargeNormalizedSlack r

/-- The four smooth branch certificates imply positive slack for the exact
piecewise coordinate. -/
theorem finalSlack_pos_of_certificate
    (hcert : FinalNumericalCertificate)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < finalSlack r (finalY r) := by
  have hM := finalM_mem_Ioo hr
  have hP := numericalP_mem_Ioo
    ⟨le_rfl, by norm_num [finalB, preliminaryB]⟩ hr
  by_cases hsmall :
      frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r
  · have ht := hcert.small_parameter_mem hr hsmall
    have hp : 0 < finalSmallRatio r := by
      by_contra h
      have hpnonpos : finalSmallRatio r ≤ 0 := le_of_not_gt h
      have htnonpos : finalSmallParameter r ≤ 0 := by
        rw [finalSmallParameter]
        exact mul_nonpos_of_nonneg_of_nonpos hr.1.le hpnonpos
      linarith [ht.1]
    rw [finalY, if_pos hsmall,
      finalSlack_small_eq_mul_normalized hr.1 hM hP hp]
    exact mul_pos hr.1 (hcert.small_slack_pos hr hsmall)
  · by_cases hmiddle : frontierA (FSlope preliminaryB) 1 ≤ finalX r
    · rw [finalY, if_neg hsmall, if_pos hmiddle,
        finalSlack_middle_eq_mul_normalized hr.1 hM hP]
      exact mul_pos hr.1 (hcert.middle_slack_pos hr hsmall hmiddle)
    · have hlarge :
          finalX r < frontierA (FSlope preliminaryB) 1 := lt_of_not_ge hmiddle
      by_cases hcap : r ≤ (361 / 1000 : ℝ)
      · rw [finalY, if_neg hsmall, if_neg hmiddle, if_pos hcap,
          finalSlack_largeCap_eq_mul_normalized hr.1 hM hP]
        exact mul_pos hr.1 (hcert.large_cap_slack_pos hr hlarge hcap)
      · have hcut : (361 / 1000 : ℝ) < r := lt_of_not_ge hcap
        rw [finalY, if_neg hsmall, if_neg hmiddle, if_neg hcap,
          finalSlack_large_eq_mul_normalized hr.1 hM hP]
        exact mul_pos hr.1 (hcert.large_slack_pos hr hcut hlarge)

/-- A completed numerical certificate gives the pointwise final descent
inequality together with its valid asymptotic-region coordinate. -/
theorem final_descent_of_certificate
    (hF : UniformRamseyExpBound (F preliminaryB))
    (hcert : FinalNumericalCertificate)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    finalY r ∈ Ioo (0 : ℝ) 1 ∧
      (finalX r, finalY r) ∈ asymptoticRegion ∧
      denseCaseExponent (finalX r) (finalM r) (finalY r) r <
        F finalB r := by
  have hregion := finalY_mem_asymptoticRegion hF hcert.toFinalRegionCertificate hr
  refine ⟨hregion.1, hregion.2, ?_⟩
  rw [denseCaseExponent_final_eq]
  exact sub_lt_self _ (finalSlack_pos_of_certificate hcert hr)

end

end RamseyLean















