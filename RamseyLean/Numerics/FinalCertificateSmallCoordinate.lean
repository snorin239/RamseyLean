import RamseyLean.Numerics.FinalCertificateSmall

/-!
# Cancellation-free small-branch coordinate certificates

The direct logarithmic coordinate gap vanishes at `r = 0`, which gives a poor
interval enclosure on the first mesh cell.  This module divides out the known
factor `r` and certifies the resulting smooth expression instead.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open FixedPointInterval

noncomputable section

/-- The polynomial factor in `preliminaryFrontierS t = t^2 * factor t`. -/
def finalSmallCoordinateFactor (t : ℝ) : ℝ :=
  (13 / 40 : ℝ) + (17 / 200 : ℝ) * t - (2 / 25 : ℝ) * t ^ 2

/-- The small-branch log-coordinate gap after division by `r`. -/
def finalSmallCoordinateNormalizedGap (r : ℝ) : ℝ :=
  finalU r - finalSmallRatio r *
      CertifiedNumerics.logOnePlusRatio (finalSmallParameter r) +
    r * finalSmallRatio r ^ 2 * Real.exp (-finalSmallParameter r) *
      finalSmallCoordinateFactor (finalSmallParameter r)

/-- Exact cancellation of the factor `r` in the small-branch coordinate gap. -/
theorem finalSmall_coordinateGap_eq_mul_normalized {r : ℝ}
    (hr : 0 < r) (hs : 0 < finalSmallRatio r) :
    r * finalSmallCoordinateNormalizedGap r =
      r * finalU r - Real.log (1 + finalSmallParameter r) +
        Real.exp (-finalSmallParameter r) *
          preliminaryFrontierS (finalSmallParameter r) := by
  have ht : finalSmallParameter r ≠ 0 := by
    rw [finalSmallParameter]
    exact mul_ne_zero hr.ne' hs.ne'
  unfold finalSmallCoordinateNormalizedGap
  rw [CertifiedNumerics.logOnePlusRatio_eq_of_ne ht]
  unfold finalSmallCoordinateFactor preliminaryFrontierS finalSmallParameter
  field_simp [hr.ne', hs.ne']

/-- Fixed-point DAG for the cancellation-free coordinate gap. -/
structure SmallCoordinateData where
  small : SmallData
  parameter2 : Interval
  qt : Interval
  ratioQt : Interval
  ratio2 : Interval
  rRatio2 : Interval
  factor : Interval
  expFactor : Interval
  positiveTerm : Interval
  normalizedGap : Interval

/-- Evaluate the cancellation-free small-coordinate DAG. -/
def smallCoordinateData (band : SmallBand) (input : Interval) : SmallCoordinateData :=
  let small := smallData band input
  let parameter2 := mulNonneg small.parameter small.parameter
  let qt := q 16 small.parameter
  let ratioQt := mulNonneg small.ratio qt
  let ratio2 := mulNonneg small.ratio small.ratio
  let rRatio2 := mulNonneg input ratio2
  let factor := add (add (rationalInterval 13 40)
      (mul (rationalInterval 17 200) small.parameter))
    (mul (rationalInterval (-2) 25) parameter2)
  let expFactor := mul small.expNegT factor
  let positiveTerm := mul rRatio2 expFactor
  let normalizedGap := add (sub small.common.u ratioQt) positiveTerm
  ⟨small, parameter2, qt, ratioQt, ratio2, rRatio2, factor, expFactor,
    positiveTerm, normalizedGap⟩

/-- Boolean side conditions for the cancellation-free small-coordinate DAG. -/
def SmallCoordinateData.safe (d : SmallCoordinateData) : Bool :=
  d.small.safe && qtSafe 16 d.small.parameter && nonneg d.qt &&
    nonneg d.ratio2

/-- Propositional decoding of the coordinate side conditions. -/
structure SmallCoordinateData.Checks (d : SmallCoordinateData) : Prop where
  smallSafe : d.small.safe = true
  qSafe : qtSafe 16 d.small.parameter = true
  qNonneg : nonneg d.qt = true
  ratio2Nonneg : nonneg d.ratio2 = true

theorem SmallCoordinateData.checks_of_safe {d : SmallCoordinateData}
    (h : d.safe = true) : d.Checks := by
  simp only [SmallCoordinateData.safe, Bool.and_eq_true] at h
  constructor <;> aesop

/-- Local transition equations for the coordinate DAG. -/
structure SmallCoordinateData.WellFormed (d : SmallCoordinateData) : Prop where
  small : d.small.WellFormed
  parameter2 : d.parameter2 = mulNonneg d.small.parameter d.small.parameter
  qt : d.qt = q 16 d.small.parameter
  ratioQt : d.ratioQt = mulNonneg d.small.ratio d.qt
  ratio2 : d.ratio2 = mulNonneg d.small.ratio d.small.ratio
  rRatio2 : d.rRatio2 = mulNonneg d.small.input d.ratio2
  factor : d.factor = add (add (rationalInterval 13 40)
      (mul (rationalInterval 17 200) d.small.parameter))
    (mul (rationalInterval (-2) 25) d.parameter2)
  expFactor : d.expFactor = mul d.small.expNegT d.factor
  positiveTerm : d.positiveTerm = mul d.rRatio2 d.expFactor
  normalizedGap : d.normalizedGap =
    add (sub d.small.common.u d.ratioQt) d.positiveTerm

theorem smallCoordinateData_wellFormed (band : SmallBand) (input : Interval) :
    (smallCoordinateData band input).WellFormed := by
  constructor
  · exact smallData_wellFormed band input
  all_goals rfl

/-- Real semantics of a cancellation-free coordinate row. -/
structure SmallCoordinateData.Sound (d : SmallCoordinateData) (r : ℝ) : Prop where
  small : d.small.Sound r
  normalizedGap : d.normalizedGap.Contains (finalSmallCoordinateNormalizedGap r)

/-- Soundness of every named transition in the cancellation-free coordinate DAG. -/
theorem SmallCoordinateData.sound {d : SmallCoordinateData} {r : ℝ}
    (hw : d.WellFormed) (hc : d.Checks) (hr : d.small.input.Contains r)
    (hrpos : 0 < r) (hband : d.small.band.Matches r) : d.Sound r := by
  have hSmallChecks := SmallData.checks_of_safe hc.smallSafe
  have hSmall := SmallData.sound hw.small hSmallChecks hr hrpos hband
  have hCommonChecks := CommonData.checks_of_safe hSmallChecks.commonSafe
  have hInputNonneg : 0 ≤ d.small.input.lo := by
    have hinput : d.small.common.input = d.small.input := by
      rw [hw.small.common]
      rfl
    rw [← hinput]
    simpa only [nonneg, decide_eq_true_eq] using hCommonChecks.inputNonneg
  have hRatioNonneg : 0 ≤ d.small.ratio.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hSmallChecks.ratioNonneg
  have hParameterNonneg : 0 ≤ d.small.parameter.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hSmallChecks.parameterNonneg
  have hQtNonneg : 0 ≤ d.qt.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.qNonneg
  have hRatio2Nonneg : 0 ≤ d.ratio2.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.ratio2Nonneg
  have hratio0 : d.small.ratio.Contains
      (smallRatioValue d.small.band r) := by
    rw [hw.small.ratio]
    exact smallRatio_contains d.small.band hr
  have hratio : d.small.ratio.Contains (finalSmallRatio r) := by
    simpa only [smallRatioValue_eq_final hband] using hratio0
  have hparameter := hSmall.parameter
  have hparameter2 : d.parameter2.Contains (finalSmallParameter r ^ 2) := by
    rw [hw.parameter2]
    convert hparameter.mulNonneg hparameter hParameterNonneg hParameterNonneg using 1 <;>
      ring
  have hqt : d.qt.Contains
      (CertifiedNumerics.logOnePlusRatio (finalSmallParameter r)) := by
    rw [hw.qt]
    exact FixedPointInterval.Sound.contains_q_of_safe hparameter hc.qSafe
  have hratioQt : d.ratioQt.Contains
      (finalSmallRatio r *
        CertifiedNumerics.logOnePlusRatio (finalSmallParameter r)) := by
    rw [hw.ratioQt]
    exact hratio.mulNonneg hqt hRatioNonneg hQtNonneg
  have hratio2 : d.ratio2.Contains (finalSmallRatio r ^ 2) := by
    rw [hw.ratio2]
    convert hratio.mulNonneg hratio hRatioNonneg hRatioNonneg using 1 <;> ring
  have hrRatio2 : d.rRatio2.Contains (r * finalSmallRatio r ^ 2) := by
    rw [hw.rRatio2]
    exact hr.mulNonneg hratio2 hInputNonneg hRatio2Nonneg
  have h13 := rationalInterval_contains 13 (q := 40) (by norm_num)
  have h17 := rationalInterval_contains 17 (q := 200) (by norm_num)
  have hn2 := rationalInterval_contains (-2) (q := 25) (by norm_num)
  have hfactor : d.factor.Contains
      (finalSmallCoordinateFactor (finalSmallParameter r)) := by
    rw [hw.factor]
    unfold finalSmallCoordinateFactor
    convert (h13.add (h17.mul hparameter)).add (hn2.mul hparameter2) using 1 <;>
      ring
  have hnegT : d.small.negT.Contains (-finalSmallParameter r) := by
    rw [hw.small.negT]
    exact hparameter.neg
  have hexp : d.small.expNegT.Contains
      (Real.exp (-finalSmallParameter r)) := by
    rw [hw.small.expNegT]
    exact FixedPointInterval.Sound.contains_exp_of_safe hnegT hSmallChecks.expNegTSafe
  have hexpFactor : d.expFactor.Contains
      (Real.exp (-finalSmallParameter r) *
        finalSmallCoordinateFactor (finalSmallParameter r)) := by
    rw [hw.expFactor]
    exact hexp.mul hfactor
  have hpositiveTerm : d.positiveTerm.Contains
      (r * finalSmallRatio r ^ 2 * Real.exp (-finalSmallParameter r) *
        finalSmallCoordinateFactor (finalSmallParameter r)) := by
    rw [hw.positiveTerm]
    convert hrRatio2.mul hexpFactor using 1 <;> ring
  have hCommonWF : d.small.common.WellFormed := by
    rw [hw.small.common]
    exact commonData_wellFormed d.small.input
  have hrCommon : d.small.common.input.Contains r := by
    rw [hw.small.common]
    exact hr
  have hCommon := CommonData.sound hCommonWF hCommonChecks hrCommon hrpos
  have hgap : d.normalizedGap.Contains (finalSmallCoordinateNormalizedGap r) := by
    rw [hw.normalizedGap]
    unfold finalSmallCoordinateNormalizedGap
    convert (sub_contains hCommon.u hratioQt).add hpositiveTerm using 1 <;> ring
  exact ⟨hSmall, hgap⟩

end

end RamseyLean.FinalCertificate
