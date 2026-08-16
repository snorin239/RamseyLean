import RamseyLean.Numerics.FinalCertificateSmallCoordinate

/-!
# Quotient enclosure for the normalized small coordinate

Near `t = 1` the origin-centered alternating-series error for
`log (1+t) / t` is intentionally coarse.  On cells bounded away from zero we
instead enclose the same function as a certified logarithm times `t⁻¹`.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open FixedPointInterval

noncomputable section

/-- Fixed-point DAG using `log (1+t) * t⁻¹` for the normalized logarithm. -/
structure SmallCoordinateQuotientData where
  small : SmallData
  parameter2 : Interval
  invParameter : Interval
  qt : Interval
  ratioQt : Interval
  ratio2 : Interval
  rRatio2 : Interval
  factor : Interval
  expFactor : Interval
  positiveTerm : Interval
  normalizedGap : Interval

def smallCoordinateQuotientData (band : SmallBand) (input : Interval) :
    SmallCoordinateQuotientData :=
  let small := smallData band input
  let parameter2 := mulNonneg small.parameter small.parameter
  let invParameter := inv small.parameter
  let qt := mulNonneg small.logOnePlusT invParameter
  let ratioQt := mulNonneg small.ratio qt
  let ratio2 := mulNonneg small.ratio small.ratio
  let rRatio2 := mulNonneg input ratio2
  let factor := add (add (rationalInterval 13 40)
      (mul (rationalInterval 17 200) small.parameter))
    (mul (rationalInterval (-2) 25) parameter2)
  let expFactor := mul small.expNegT factor
  let positiveTerm := mul rRatio2 expFactor
  let normalizedGap := add (sub small.common.u ratioQt) positiveTerm
  ⟨small, parameter2, invParameter, qt, ratioQt, ratio2, rRatio2, factor,
    expFactor, positiveTerm, normalizedGap⟩

def SmallCoordinateQuotientData.safe (d : SmallCoordinateQuotientData) : Bool :=
  d.small.safe && positive d.small.parameter && nonneg d.small.logOnePlusT &&
    nonneg d.invParameter && nonneg d.qt && nonneg d.ratio2

structure SmallCoordinateQuotientData.Checks
    (d : SmallCoordinateQuotientData) : Prop where
  smallSafe : d.small.safe = true
  parameterPositive : positive d.small.parameter = true
  logNonneg : nonneg d.small.logOnePlusT = true
  invNonneg : nonneg d.invParameter = true
  qNonneg : nonneg d.qt = true
  ratio2Nonneg : nonneg d.ratio2 = true

theorem SmallCoordinateQuotientData.checks_of_safe
    {d : SmallCoordinateQuotientData} (h : d.safe = true) : d.Checks := by
  simp only [SmallCoordinateQuotientData.safe, Bool.and_eq_true] at h
  constructor <;> aesop

structure SmallCoordinateQuotientData.WellFormed
    (d : SmallCoordinateQuotientData) : Prop where
  small : d.small.WellFormed
  parameter2 : d.parameter2 = mulNonneg d.small.parameter d.small.parameter
  invParameter : d.invParameter = inv d.small.parameter
  qt : d.qt = mulNonneg d.small.logOnePlusT d.invParameter
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

theorem smallCoordinateQuotientData_wellFormed
    (band : SmallBand) (input : Interval) :
    (smallCoordinateQuotientData band input).WellFormed := by
  constructor
  · exact smallData_wellFormed band input
  all_goals rfl

structure SmallCoordinateQuotientData.Sound
    (d : SmallCoordinateQuotientData) (r : ℝ) : Prop where
  small : d.small.Sound r
  normalizedGap : d.normalizedGap.Contains (finalSmallCoordinateNormalizedGap r)

theorem SmallCoordinateQuotientData.sound
    {d : SmallCoordinateQuotientData} {r : ℝ}
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
  have hParameterPositive : 0 < d.small.parameter.lo := by
    simpa only [positive, decide_eq_true_eq] using hc.parameterPositive
  have hLogNonneg : 0 ≤ d.small.logOnePlusT.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.logNonneg
  have hInvNonneg : 0 ≤ d.invParameter.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.invNonneg
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
  have hparameterInv : d.invParameter.Contains (finalSmallParameter r)⁻¹ := by
    rw [hw.invParameter]
    exact hparameter.inv hParameterPositive
  have hOnePlusT : d.small.onePlusT.Contains
      (1 + finalSmallParameter r) := by
    have hone : (point scale).Contains (1 : ℝ) := by
      have h := Interval.contains_point scale
      convert h using 1
      norm_num [FixedPointInterval.value, scale]
    rw [hw.small.onePlusT]
    exact hone.add hparameter
  have hLogOnePlusT : d.small.logOnePlusT.Contains
      (Real.log (1 + finalSmallParameter r)) := by
    rw [hw.small.logOnePlusT]
    exact FixedPointInterval.Sound.contains_log_of_safe hOnePlusT
      hSmallChecks.logOnePlusTSafe
  have hqt0 : d.qt.Contains
      (Real.log (1 + finalSmallParameter r) * (finalSmallParameter r)⁻¹) := by
    rw [hw.qt]
    exact hLogOnePlusT.mulNonneg hparameterInv hLogNonneg hInvNonneg
  have htne : finalSmallParameter r ≠ 0 := by
    unfold finalSmallParameter
    exact mul_ne_zero hrpos.ne' hSmall.ratioPos.ne'
  have hqt : d.qt.Contains
      (CertifiedNumerics.logOnePlusRatio (finalSmallParameter r)) := by
    rw [CertifiedNumerics.logOnePlusRatio_eq_of_ne htne]
    simpa only [div_eq_mul_inv] using hqt0
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
