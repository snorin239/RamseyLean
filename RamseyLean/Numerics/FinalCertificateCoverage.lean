import RamseyLean.Numerics.FinalCertificateRowsBranches
import RamseyLean.Numerics.FinalCertificateMesh

/-!
# Continuum soundness of the final numerical rows

This module is the semantic boundary between generated fixed-point literals
and the real inequalities required by the final descent.  It contains no
large closed computation: each row check is decoded through the named DAG
soundness theorems, and uniform-mesh lemmas select a row for an arbitrary
real input.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

noncomputable section

private theorem finalU_mul_eq_neg_log {r : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    r * finalU r = -Real.log (finalX r) := by
  have hM := finalM_mem_Ioo hr
  have hP := numericalP_mem_Ioo
    ⟨le_rfl, by norm_num [finalB, preliminaryB]⟩ hr
  rw [finalU_eq_neg_log_div hr.1 hM hP]
  field_simp [hr.1.ne']

private theorem finalX_le_frontierB_of_gap {r t : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1)
    (hgap : 0 ≤ r * finalU r - Real.log (1 + t) +
      Real.exp (-t) * preliminaryFrontierS t) :
    finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB) t := by
  have hlog : Real.log (finalX r) ≤
      Real.log (frontierB (F preliminaryB) (FSlope preliminaryB) t) := by
    rw [log_frontierB_preliminary]
    rw [finalU_mul_eq_neg_log hr] at hgap
    linarith
  have hXpos := (finalX_mem_Ioo hr).1
  have hfrontPos :
      0 < frontierB (F preliminaryB) (FSlope preliminaryB) t := by
    unfold frontierB
    exact Real.exp_pos _
  rw [← Real.exp_log hXpos, ← Real.exp_log hfrontPos]
  exact Real.exp_le_exp.mpr hlog

private theorem frontierB_lt_finalX_of_gap_neg {r t : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1)
    (hgap : r * finalU r - Real.log (1 + t) +
      Real.exp (-t) * preliminaryFrontierS t < 0) :
    frontierB (F preliminaryB) (FSlope preliminaryB) t < finalX r := by
  have hlog : Real.log
      (frontierB (F preliminaryB) (FSlope preliminaryB) t) <
      Real.log (finalX r) := by
    rw [log_frontierB_preliminary]
    rw [finalU_mul_eq_neg_log hr] at hgap
    linarith
  have hXpos := (finalX_mem_Ioo hr).1
  have hfrontPos :
      0 < frontierB (F preliminaryB) (FSlope preliminaryB) t := by
    unfold frontierB
    exact Real.exp_pos _
  rw [← Real.exp_log hfrontPos, ← Real.exp_log hXpos]
  exact Real.exp_lt_exp.mpr hlog

private theorem finalX_le_frontierA_of_gap {r t : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1)
    (hgap : 0 ≤ r * finalU r + Real.log t - Real.log (1 + t) -
      Real.exp (-t) * preliminaryFrontierR t) :
    finalX r ≤ frontierA (FSlope preliminaryB) t := by
  have hlog : Real.log (finalX r) ≤
      Real.log (frontierA (FSlope preliminaryB) t) := by
    rw [log_frontierA_preliminary]
    rw [finalU_mul_eq_neg_log hr] at hgap
    linarith
  have hXpos := (finalX_mem_Ioo hr).1
  have hfrontPos : 0 < frontierA (FSlope preliminaryB) t := by
    unfold frontierA
    exact Real.exp_pos _
  rw [← Real.exp_log hXpos, ← Real.exp_log hfrontPos]
  exact Real.exp_le_exp.mpr hlog

private theorem frontierA_le_finalX_of_gap_nonpos {r t : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1)
    (hgap : r * finalU r + Real.log t - Real.log (1 + t) -
      Real.exp (-t) * preliminaryFrontierR t ≤ 0) :
    frontierA (FSlope preliminaryB) t ≤ finalX r := by
  have hlog : Real.log (frontierA (FSlope preliminaryB) t) ≤
      Real.log (finalX r) := by
    rw [log_frontierA_preliminary]
    rw [finalU_mul_eq_neg_log hr] at hgap
    linarith
  have hXpos := (finalX_mem_Ioo hr).1
  have hfrontPos : 0 < frontierA (FSlope preliminaryB) t := by
    unfold frontierA
    exact Real.exp_pos _
  rw [← Real.exp_log hfrontPos, ← Real.exp_log hXpos]
  exact Real.exp_le_exp.mpr hlog

private theorem finalX_lt_frontierA_of_gap_pos {r t : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1)
    (hgap : 0 < r * finalU r + Real.log t - Real.log (1 + t) -
      Real.exp (-t) * preliminaryFrontierR t) :
    finalX r < frontierA (FSlope preliminaryB) t := by
  have hlog : Real.log (finalX r) <
      Real.log (frontierA (FSlope preliminaryB) t) := by
    rw [log_frontierA_preliminary]
    rw [finalU_mul_eq_neg_log hr] at hgap
    linarith
  have hXpos := (finalX_mem_Ioo hr).1
  have hfrontPos : 0 < frontierA (FSlope preliminaryB) t := by
    unfold frontierA
    exact Real.exp_pos _
  rw [← Real.exp_log hXpos, ← Real.exp_log hfrontPos]
  exact Real.exp_lt_exp.mpr hlog

private theorem value_hi_le_one {I : Interval} (h : I.hi ≤ scale) :
    value I.hi ≤ (1 : ℝ) := by
  unfold value
  have h' : (I.hi : ℝ) ≤ (scale : ℝ) := by exact_mod_cast h
  calc
    (I.hi : ℝ) / (scale : ℝ) ≤ (scale : ℝ) / (scale : ℝ) :=
      div_le_div_of_nonneg_right h' scale_pos_real.le
    _ = 1 := by field_simp [scale_pos_real.ne']

/-- A checked origin-series small row proves all three small-branch
obligations throughout its input interval. -/
theorem small_of_check {d : SmallCoordinateData} {r : ℝ}
    (hcheck : smallCoordinateCheck d = true)
    (hrI : d.small.input.Contains r) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hband : d.small.band.Matches r) :
    finalSmallParameter r ∈ Ioc (0 : ℝ) 1 ∧
      finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB)
        (finalSmallParameter r) ∧
      0 < finalSmallNormalizedSlack r := by
  have hfacts := smallRowFacts_of_check hcheck
  have hsound := SmallCoordinateData.sound hfacts.wellFormed hfacts.checks
    hrI hr.1 hband
  have hsmallChecks := SmallData.checks_of_safe hfacts.checks.smallSafe
  have hslack : 0 < finalSmallNormalizedSlack r := by
    have h := value_lt_of_checkLower hfacts.slackPositive hsound.small.slack
    simpa [value] using h
  have hnorm : 0 < finalSmallCoordinateNormalizedGap r := by
    have h := value_lt_of_checkLower hfacts.coordinatePositive
      hsound.normalizedGap
    simpa [value] using h
  have hcoordinateGap :
      0 < r * finalU r - Real.log (1 + finalSmallParameter r) +
        Real.exp (-finalSmallParameter r) *
          preliminaryFrontierS (finalSmallParameter r) := by
    rw [← finalSmall_coordinateGap_eq_mul_normalized hr.1
      hsound.small.ratioPos]
    exact mul_pos hr.1 hnorm
  have hparameter : finalSmallParameter r ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · rw [finalSmallParameter]
      exact mul_pos hr.1 hsound.small.ratioPos
    · exact hsound.small.parameter.2.trans
        (value_hi_le_one hsmallChecks.parameterUpper)
  exact ⟨hparameter,
    finalX_le_frontierB_of_gap hr hcoordinateGap.le, hslack⟩

/-- The direct-logarithm small row has the same real conclusion as the
origin-series row. -/
theorem small_of_quotient_check {d : SmallCoordinateQuotientData} {r : ℝ}
    (hcheck : smallCoordinateQuotientCheck d = true)
    (hrI : d.small.input.Contains r) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hband : d.small.band.Matches r) :
    finalSmallParameter r ∈ Ioc (0 : ℝ) 1 ∧
      finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB)
        (finalSmallParameter r) ∧
      0 < finalSmallNormalizedSlack r := by
  have hfacts := smallQuotientRowFacts_of_check hcheck
  have hsound := SmallCoordinateQuotientData.sound hfacts.wellFormed
    hfacts.checks hrI hr.1 hband
  have hsmallChecks := SmallData.checks_of_safe hfacts.checks.smallSafe
  have hslack : 0 < finalSmallNormalizedSlack r := by
    have h := value_lt_of_checkLower hfacts.slackPositive hsound.small.slack
    simpa [value] using h
  have hnorm : 0 < finalSmallCoordinateNormalizedGap r := by
    have h := value_lt_of_checkLower hfacts.coordinatePositive
      hsound.normalizedGap
    simpa [value] using h
  have hcoordinateGap :
      0 < r * finalU r - Real.log (1 + finalSmallParameter r) +
        Real.exp (-finalSmallParameter r) *
          preliminaryFrontierS (finalSmallParameter r) := by
    rw [← finalSmall_coordinateGap_eq_mul_normalized hr.1
      hsound.small.ratioPos]
    exact mul_pos hr.1 hnorm
  have hparameter : finalSmallParameter r ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · rw [finalSmallParameter]
      exact mul_pos hr.1 hsound.small.ratioPos
    · exact hsound.small.parameter.2.trans
        (value_hi_le_one hsmallChecks.parameterUpper)
  exact ⟨hparameter,
    finalX_le_frontierB_of_gap hr hcoordinateGap.le, hslack⟩

theorem middle_pos_of_check {d : MiddleData} {r : ℝ}
    (hcheck : middleCheck d = true) (hrI : d.input.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < finalMiddleNormalizedSlack r := by
  have hfacts := middleRowFacts_of_check hcheck
  have hsound := MiddleData.sound hfacts.wellFormed hfacts.checks hrI hr.1
  have h := value_lt_of_checkLower hfacts.slackPositive hsound
  simpa [value] using h

theorem cap_pos_of_check {d : LargeData} {r : ℝ}
    (hcheck : capCheck d = true) (hrI : d.input.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < finalLargeCapNormalizedSlack r := by
  have hfacts := capRowFacts_of_check hcheck
  have hone : (point scale).Contains (1 : ℝ) := by
    have h := Interval.contains_point scale
    convert h using 1
    norm_num [value, scale]
  have hsound := LargeData.sound hfacts.wellFormed hfacts.checks hrI
    (by simpa only [hfacts.parameter] using hone) hr.1
  have h := value_lt_of_checkLower hfacts.slackPositive hsound.slack
  rw [largeNormalizedSlackAt_one] at h
  simpa [value] using h

/-- A checked raw-large row proves parameter range, coordinate admissibility,
and positive normalized slack. -/
theorem large_of_check {band : LargeBand} {d : LargeData} {r : ℝ}
    (hcheck : largeCheck band d = true) (hrI : d.input.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hband : band.Matches r) :
    finalLargeParameter r ∈ Ioc (0 : ℝ) 1 ∧
      finalX r ≤ frontierA (FSlope preliminaryB) (finalLargeParameter r) ∧
      0 < finalLargeNormalizedSlack r := by
  have hfacts := largeRowFacts_of_check hcheck
  have ht0 : (largeParameter band d.input).Contains
      (largeParameterValue band r) := largeParameter_contains band hrI
  have ht : d.parameter.Contains (largeParameterValue band r) := by
    rw [hfacts.parameter]
    exact ht0
  have hsound := LargeData.sound hfacts.wellFormed hfacts.checks hrI ht hr.1
  have hparameterEq := largeParameterValue_eq_final hband
  have hslack0 : 0 < largeNormalizedSlackAt r
      (largeParameterValue band r) := by
    have h := value_lt_of_checkLower hfacts.slackPositive hsound.slack
    simpa [value] using h
  have hcoord0 : 0 < r * finalU r + Real.log (largeParameterValue band r) -
      Real.log (1 + largeParameterValue band r) -
      Real.exp (-largeParameterValue band r) *
        preliminaryFrontierR (largeParameterValue band r) := by
    have h := value_lt_of_checkLower hfacts.coordinatePositive
      hsound.coordinateGap
    simpa [value] using h
  have hparameter : finalLargeParameter r ∈ Ioc (0 : ℝ) 1 := by
    rw [← hparameterEq]
    exact ⟨hsound.parameterPos,
      ht.2.trans (value_hi_le_one hfacts.checks.parameterUpper)⟩
  rw [hparameterEq] at hcoord0 hslack0
  rw [largeNormalizedSlackAt_final] at hslack0
  exact ⟨hparameter, finalX_le_frontierA_of_gap hr hcoord0.le, hslack0⟩

theorem crossing_bBelow_of_check {d : CrossingData} {r : ℝ}
    (hcheck : crossingCheck d = true) (hrI : d.input.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hhi : d.input.hi ≤ 257800000000) :
    frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r := by
  have hfacts := crossingRowFacts_of_check hcheck
  have hsound := CrossingData.sound hfacts.wellFormed hfacts.checks
    hrI hr.1
  have hneg : 0 < -(r * finalU r - Real.log (2 : ℝ) +
      Real.exp (-(1 : ℝ)) * preliminaryFrontierS 1) := by
    have h := value_lt_of_checkLower (hfacts.bBelow hhi) hsound.bGap.neg
    simpa [value] using h
  apply frontierB_lt_finalX_of_gap_neg hr
  norm_num
  linarith

theorem crossing_bAbove_of_check {d : CrossingData} {r : ℝ}
    (hcheck : crossingCheck d = true) (hrI : d.input.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hlo : 258000000000 ≤ d.input.lo) :
    finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB) 1 := by
  have hfacts := crossingRowFacts_of_check hcheck
  have hsound := CrossingData.sound hfacts.wellFormed hfacts.checks
    hrI hr.1
  have hgap : 0 ≤ r * finalU r - Real.log (2 : ℝ) +
      Real.exp (-(1 : ℝ)) * preliminaryFrontierS 1 := by
    have h := value_le_of_checkLowerEq (hfacts.bAbove hlo) hsound.bGap
    simpa [value] using h
  apply finalX_le_frontierB_of_gap hr
  norm_num
  exact hgap

theorem crossing_aBelow_of_check {d : CrossingData} {r : ℝ}
    (hcheck : crossingCheck d = true) (hrI : d.input.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hhi : d.input.hi ≤ 360400000000) :
    frontierA (FSlope preliminaryB) 1 ≤ finalX r := by
  have hfacts := crossingRowFacts_of_check hcheck
  have hsound := CrossingData.sound hfacts.wellFormed hfacts.checks
    hrI hr.1
  have hneg : 0 ≤ -(r * finalU r - Real.log (2 : ℝ) -
      Real.exp (-(1 : ℝ)) * preliminaryFrontierR 1) := by
    have h := value_le_of_checkLowerEq (hfacts.aBelow hhi) hsound.aGap.neg
    simpa [value] using h
  apply frontierA_le_finalX_of_gap_nonpos hr
  norm_num
  linarith

theorem crossing_aAbove_of_check {d : CrossingData} {r : ℝ}
    (hcheck : crossingCheck d = true) (hrI : d.input.Contains r)
    (hr : r ∈ Ioc (0 : ℝ) 1) (hlo : 360500000000 ≤ d.input.lo) :
    finalX r < frontierA (FSlope preliminaryB) 1 := by
  have hfacts := crossingRowFacts_of_check hcheck
  have hsound := CrossingData.sound hfacts.wellFormed hfacts.checks
    hrI hr.1
  have hgap : 0 < r * finalU r - Real.log (2 : ℝ) -
      Real.exp (-(1 : ℝ)) * preliminaryFrontierR 1 := by
    have h := value_lt_of_checkLower (hfacts.aAbove hlo) hsound.aGap
    simpa [value] using h
  apply finalX_lt_frontierA_of_gap_pos hr
  norm_num
  linarith

/-- Lift origin-series small rows over a uniform fixed-point band. -/
theorem small_on_uniform_band {start step : ℤ} {N : ℕ} {band : SmallBand}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : SmallCoordinateData,
      d.small.input = uniformCell start step k ∧
        d.small.band = band ∧ smallCoordinateCheck d = true)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) (hband : band.Matches r) :
    finalSmallParameter r ∈ Ioc (0 : ℝ) 1 ∧
      finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB)
        (finalSmallParameter r) ∧
      0 < finalSmallNormalizedSlack r := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hdband, hcheck⟩ := hrows k hk
  have hrI : d.small.input.Contains r := by rw [hinput]; exact hrCell
  apply small_of_check hcheck hrI hr
  rw [hdband]
  exact hband

/-- Lift direct-logarithm small rows over a uniform fixed-point band. -/
theorem small_quotient_on_uniform_band {start step : ℤ} {N : ℕ}
    {band : SmallBand} (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : SmallCoordinateQuotientData,
      d.small.input = uniformCell start step k ∧
        d.small.band = band ∧ smallCoordinateQuotientCheck d = true)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) (hband : band.Matches r) :
    finalSmallParameter r ∈ Ioc (0 : ℝ) 1 ∧
      finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB)
        (finalSmallParameter r) ∧
      0 < finalSmallNormalizedSlack r := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hdband, hcheck⟩ := hrows k hk
  have hrI : d.small.input.Contains r := by rw [hinput]; exact hrCell
  apply small_of_quotient_check hcheck hrI hr
  rw [hdband]
  exact hband

theorem middle_pos_on_uniform_band {start step : ℤ} {N : ℕ}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : MiddleData,
      d.input = uniformCell start step k ∧ middleCheck d = true)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < finalMiddleNormalizedSlack r := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hcheck⟩ := hrows k hk
  apply middle_pos_of_check hcheck (hr := hr)
  rw [hinput]
  exact hrCell

theorem cap_pos_on_uniform_band {start step : ℤ} {N : ℕ}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : LargeData,
      d.input = uniformCell start step k ∧ capCheck d = true)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    0 < finalLargeCapNormalizedSlack r := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hcheck⟩ := hrows k hk
  apply cap_pos_of_check hcheck (hr := hr)
  rw [hinput]
  exact hrCell

theorem large_on_uniform_band {start step : ℤ} {N : ℕ} {band : LargeBand}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : LargeData,
      d.input = uniformCell start step k ∧ largeCheck band d = true)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) (hband : band.Matches r) :
    finalLargeParameter r ∈ Ioc (0 : ℝ) 1 ∧
      finalX r ≤ frontierA (FSlope preliminaryB) (finalLargeParameter r) ∧
      0 < finalLargeNormalizedSlack r := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hcheck⟩ := hrows k hk
  have hrI : d.input.Contains r := by rw [hinput]; exact hrCell
  exact large_of_check hcheck hrI hr hband

theorem crossing_bBelow_on_uniform_band {start step : ℤ} {N : ℕ}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : CrossingData,
      d.input = uniformCell start step k ∧ crossingCheck d = true)
    (hthreshold : ∀ k : ℕ, k < N →
      (uniformCell start step k).hi ≤ 257800000000)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    frontierB (F preliminaryB) (FSlope preliminaryB) 1 < finalX r := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hcheck⟩ := hrows k hk
  apply crossing_bBelow_of_check hcheck (hr := hr)
  · rw [hinput]
    exact hrCell
  · rw [hinput]
    exact hthreshold k hk

theorem crossing_bAbove_on_uniform_band {start step : ℤ} {N : ℕ}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : CrossingData,
      d.input = uniformCell start step k ∧ crossingCheck d = true)
    (hthreshold : ∀ k : ℕ, k < N →
      258000000000 ≤ (uniformCell start step k).lo)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    finalX r ≤ frontierB (F preliminaryB) (FSlope preliminaryB) 1 := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hcheck⟩ := hrows k hk
  apply crossing_bAbove_of_check hcheck (hr := hr)
  · rw [hinput]
    exact hrCell
  · rw [hinput]
    exact hthreshold k hk

theorem crossing_aBelow_on_uniform_band {start step : ℤ} {N : ℕ}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : CrossingData,
      d.input = uniformCell start step k ∧ crossingCheck d = true)
    (hthreshold : ∀ k : ℕ, k < N →
      (uniformCell start step k).hi ≤ 360400000000)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    frontierA (FSlope preliminaryB) 1 ≤ finalX r := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hcheck⟩ := hrows k hk
  apply crossing_aBelow_of_check hcheck (hr := hr)
  · rw [hinput]
    exact hrCell
  · rw [hinput]
    exact hthreshold k hk

theorem crossing_aAbove_on_uniform_band {start step : ℤ} {N : ℕ}
    (hN : 0 < N) (hstep : 0 < step)
    (hrows : ∀ k : ℕ, k < N → ∃ d : CrossingData,
      d.input = uniformCell start step k ∧ crossingCheck d = true)
    (hthreshold : ∀ k : ℕ, k < N →
      360500000000 ≤ (uniformCell start step k).lo)
    {r : ℝ} (hrBand : r ∈ Icc (value start) (value (start + step * N)))
    (hr : r ∈ Ioc (0 : ℝ) 1) :
    finalX r < frontierA (FSlope preliminaryB) 1 := by
  obtain ⟨k, hk, hrCell⟩ := exists_uniformCell hN hstep hrBand
  obtain ⟨d, hinput, hcheck⟩ := hrows k hk
  apply crossing_aAbove_of_check hcheck (hr := hr)
  · rw [hinput]
    exact hrCell
  · rw [hinput]
    exact hthreshold k hk

end

end RamseyLean.FinalCertificate
