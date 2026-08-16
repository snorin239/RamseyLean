import RamseyLean.Numerics.FinalCertificateBranchHelpers

/-! The three small-r quartic branch certificates for the final descent. -/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

noncomputable section

def SmallBand.Matches (band : SmallBand) (r : ℝ) : Prop :=
  match band with
  | .zeroTenth => r ≤ 1 / 10
  | .tenthFifth => 1 / 10 < r ∧ r ≤ 1 / 5
  | .fifthCut => 1 / 5 < r

def smallRatioValue (band : SmallBand) (r : ℝ) : ℝ :=
  match band with
  | .zeroTenth =>
      finalQuartic (22764 / 10000) (4213 / 10000) (823 / 10000)
        (213 / 10000) (-(41 / 10000)) (10 * r)
  | .tenthFifth =>
      finalQuartic (27971 / 10000) (6328 / 10000) (1148 / 10000)
        (29 / 10000) (-(385 / 10000)) (10 * r - 1)
  | .fifthCut =>
      finalQuartic (35092 / 10000) (4307 / 10000) (-(348 / 10000))
        (-(305 / 10000)) (65 / 10000) ((50 / 3) * (r - 1 / 5))

theorem smallRatio_contains (band : SmallBand) {I : Interval} {r : ℝ}
    (hr : I.Contains r) : (smallRatio band I).Contains (smallRatioValue band r) := by
  have h1 : (rationalInterval 1 1).Contains (1 : ℝ) := by
    convert rationalInterval_contains 1 (q := 1) (by norm_num) using 1 <;> norm_num
  have h5 : (rationalInterval 1 5).Contains (1 / 5 : ℝ) := by
    convert rationalInterval_contains 1 (q := 5) (by norm_num) using 1 <;> norm_num
  cases band with
  | zeroTenth =>
      apply quartic_contains
      · exact rationalInterval_contains 22764 (q := 10000) (by norm_num)
      · exact rationalInterval_contains 4213 (q := 10000) (by norm_num)
      · exact rationalInterval_contains 823 (q := 10000) (by norm_num)
      · exact rationalInterval_contains 213 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-41) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · convert (rationalInterval_contains 10 (q := 1) (by norm_num)).mul hr using 1 <;>
          norm_num
  | tenthFifth =>
      apply quartic_contains
      · exact rationalInterval_contains 27971 (q := 10000) (by norm_num)
      · exact rationalInterval_contains 6328 (q := 10000) (by norm_num)
      · exact rationalInterval_contains 1148 (q := 10000) (by norm_num)
      · exact rationalInterval_contains 29 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-385) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · have hu := sub_contains ((rationalInterval_contains 10
          (q := 1) (by norm_num)).mul hr) h1
        convert hu using 1 <;> norm_num
  | fifthCut =>
      apply quartic_contains
      · exact rationalInterval_contains 35092 (q := 10000) (by norm_num)
      · exact rationalInterval_contains 4307 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-348) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · convert rationalInterval_contains (-305) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · exact rationalInterval_contains 65 (q := 10000) (by norm_num)
      · exact (rationalInterval_contains 50 (q := 3) (by norm_num)).mul
          (sub_contains hr h5)

theorem smallRatioValue_eq_final {band : SmallBand} {r : ℝ}
    (h : band.Matches r) : smallRatioValue band r = finalSmallRatio r := by
  cases band with
  | zeroTenth =>
      change r ≤ (1 / 10 : ℝ) at h
      rw [finalSmallRatio, if_pos h]
      rfl
  | tenthFifth =>
      change (1 / 10 : ℝ) < r ∧ r ≤ 1 / 5 at h
      have hn : ¬ r ≤ 1 / 10 := not_le.mpr h.1
      rw [finalSmallRatio, if_neg hn, if_pos h.2]
      rfl
  | fifthCut =>
      change (1 / 5 : ℝ) < r at h
      have h15 : (1 / 10 : ℝ) < 1 / 5 := by norm_num
      have hn1 : ¬ r ≤ 1 / 10 := not_le.mpr (h15.trans h)
      have hn2 : ¬ r ≤ 1 / 5 := not_le.mpr h
      rw [finalSmallRatio, if_neg hn1, if_neg hn2]
      rfl

structure SmallData where
  input : Interval
  band : SmallBand
  common : CommonData
  ratio : Interval
  parameter : Interval
  negT : Interval
  expNegT : Interval
  onePlusR : Interval
  qr : Interval
  entropy : Interval
  corr : Interval
  tail : Interval
  base : Interval
  onePlusT : Interval
  logRatio : Interval
  logOnePlusT : Interval
  expR : Interval
  logAWithoutR : Interval
  slack : Interval
  logB : Interval
  coordinateGap : Interval

def smallData (band : SmallBand) (r : Interval) : SmallData :=
  let c := commonData r
  let ratio := smallRatio band r
  let parameter := mulNonneg r ratio
  let negT := neg parameter
  let expNegT := exp 12 negT
  let onePlusR := add (point scale) r
  let qr := q 16 r
  let entropy := mulNonneg onePlusR qr
  let corr := correction r c.r2 c.expNegR
  let tail := commonTail r c.r2 c.u
  let base := add (add entropy corr) tail
  let onePlusT := add (point scale) parameter
  let logRatio := log 16 ratio
  let logOnePlusT := log 16 onePlusT
  let expR := mul expNegT (preliminaryR parameter)
  let logAWithoutR := sub (sub logRatio logOnePlusT) expR
  let slack := add base (divNat logAWithoutR 2)
  let logB := add (neg logOnePlusT)
    (mul expNegT (preliminaryS parameter))
  let coordinateGap := add (mulNonneg r c.u) logB
  ⟨r, band, c, ratio, parameter, negT, expNegT, onePlusR, qr,
    entropy, corr, tail, base, onePlusT, logRatio, logOnePlusT, expR,
    logAWithoutR, slack, logB, coordinateGap⟩

def SmallData.safe (d : SmallData) : Bool :=
  d.common.safe && nonneg d.ratio && positive d.ratio &&
  nonneg d.parameter && expSafe 12 d.negT && logSafe 16 d.ratio &&
  logSafe 16 d.onePlusT && qtSafe 16 d.input && nonneg d.qr &&
  nonneg d.onePlusR && decide (d.parameter.hi ≤ scale)

structure SmallData.Checks (d : SmallData) : Prop where
  commonSafe : d.common.safe = true
  ratioNonneg : nonneg d.ratio = true
  ratioPositive : positive d.ratio = true
  parameterNonneg : nonneg d.parameter = true
  expNegTSafe : expSafe 12 d.negT = true
  logRatioSafe : logSafe 16 d.ratio = true
  logOnePlusTSafe : logSafe 16 d.onePlusT = true
  qSafe : qtSafe 16 d.input = true
  qNonneg : nonneg d.qr = true
  onePlusRNonneg : nonneg d.onePlusR = true
  parameterUpper : d.parameter.hi ≤ scale

theorem SmallData.checks_of_safe {d : SmallData} (h : d.safe = true) : d.Checks := by
  simp only [SmallData.safe, Bool.and_eq_true, decide_eq_true_eq] at h
  constructor <;> aesop

structure SmallData.WellFormed (d : SmallData) : Prop where
  common : d.common = commonData d.input
  ratio : d.ratio = smallRatio d.band d.input
  parameter : d.parameter = mulNonneg d.input d.ratio
  negT : d.negT = neg d.parameter
  expNegT : d.expNegT = exp 12 d.negT
  onePlusR : d.onePlusR = add (point scale) d.input
  qr : d.qr = q 16 d.input
  entropy : d.entropy = mulNonneg d.onePlusR d.qr
  corr : d.corr = correction d.input d.common.r2 d.common.expNegR
  tail : d.tail = commonTail d.input d.common.r2 d.common.u
  base : d.base = add (add d.entropy d.corr) d.tail
  onePlusT : d.onePlusT = add (point scale) d.parameter
  logRatio : d.logRatio = log 16 d.ratio
  logOnePlusT : d.logOnePlusT = log 16 d.onePlusT
  expR : d.expR = mul d.expNegT (preliminaryR d.parameter)
  logAWithoutR : d.logAWithoutR = sub (sub d.logRatio d.logOnePlusT) d.expR
  slack : d.slack = add d.base (divNat d.logAWithoutR 2)
  logB : d.logB = add (neg d.logOnePlusT)
    (mul d.expNegT (preliminaryS d.parameter))
  coordinateGap : d.coordinateGap = add (mulNonneg d.input d.common.u) d.logB

theorem smallData_wellFormed (band : SmallBand) (I : Interval) :
    (smallData band I).WellFormed := by
  constructor <;> rfl

structure SmallData.Sound (d : SmallData) (r : ℝ) : Prop where
  parameter : d.parameter.Contains (finalSmallParameter r)
  coordinateGap : d.coordinateGap.Contains
    (r * finalU r - Real.log (1 + finalSmallParameter r) +
      Real.exp (-finalSmallParameter r) *
        preliminaryFrontierS (finalSmallParameter r))
  slack : d.slack.Contains (finalSmallNormalizedSlack r)
  ratioPos : 0 < finalSmallRatio r

theorem SmallData.sound {d : SmallData} {r : ℝ}
    (hw : d.WellFormed) (hc : d.Checks) (hr : d.input.Contains r)
    (hrpos : 0 < r) (hband : d.band.Matches r) : d.Sound r := by
  have hRatioNonneg : 0 ≤ d.ratio.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.ratioNonneg
  have hRatioPositive : 0 < d.ratio.lo := by
    simpa only [positive, decide_eq_true_eq] using hc.ratioPositive
  have hParameterNonneg : 0 ≤ d.parameter.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.parameterNonneg
  have hQrNonneg : 0 ≤ d.qr.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.qNonneg
  have hOnePlusRNonneg : 0 ≤ d.onePlusR.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.onePlusRNonneg
  have hone : (point scale).Contains (1 : ℝ) := by
    have h := Interval.contains_point scale
    convert h using 1
    norm_num [FixedPointInterval.value, scale]
  have hCommonWF : d.common.WellFormed := by
    rw [hw.common]
    exact commonData_wellFormed d.input
  have hCommonChecks : d.common.Checks := CommonData.checks_of_safe hc.commonSafe
  have hCommonInput : d.common.input = d.input := by rw [hw.common]; rfl
  have hInputNonneg : 0 ≤ d.input.lo := by
    rw [← hCommonInput]
    simpa only [nonneg, decide_eq_true_eq] using hCommonChecks.inputNonneg
  have hrCommon : d.common.input.Contains r := by simpa only [hCommonInput] using hr
  have hCommon := CommonData.sound hCommonWF hCommonChecks hrCommon hrpos
  have hratio0 : d.ratio.Contains (smallRatioValue d.band r) := by
    rw [hw.ratio]
    exact smallRatio_contains d.band hr
  have hratio : d.ratio.Contains (finalSmallRatio r) := by
    simpa only [smallRatioValue_eq_final hband] using hratio0
  have hratioPos : 0 < finalSmallRatio r := by
    have hv : 0 < FixedPointInterval.value d.ratio.lo := by
      unfold FixedPointInterval.value
      exact div_pos (by exact_mod_cast hRatioPositive) scale_pos_real
    exact hv.trans_le hratio.1
  have hparameter : d.parameter.Contains (finalSmallParameter r) := by
    rw [hw.parameter]
    simpa only [finalSmallParameter] using
      hr.mulNonneg hratio hInputNonneg hRatioNonneg
  have hnegT : d.negT.Contains (-finalSmallParameter r) := by
    rw [hw.negT]
    exact hparameter.neg
  have hexpNegT : d.expNegT.Contains (Real.exp (-finalSmallParameter r)) := by
    rw [hw.expNegT]
    exact FixedPointInterval.Sound.contains_exp_of_safe hnegT hc.expNegTSafe
  have hOnePlusR : d.onePlusR.Contains (1 + r) := by
    rw [hw.onePlusR]
    exact hone.add hr
  have hqr : d.qr.Contains (CertifiedNumerics.logOnePlusRatio r) := by
    rw [hw.qr]
    exact FixedPointInterval.Sound.contains_q_of_safe hr hc.qSafe
  have hEntropy : d.entropy.Contains
      ((1 + r) * CertifiedNumerics.logOnePlusRatio r) := by
    rw [hw.entropy]
    exact hOnePlusR.mulNonneg hqr hOnePlusRNonneg hQrNonneg
  have hCorr := correction_contains hr hCommon.r2 hCommon.expNegR
  rw [← hw.corr] at hCorr
  have hTail := commonTail_contains hr hCommon.r2 hCommon.u
  rw [← hw.tail] at hTail
  have hBase : d.base.Contains
      ((1 + r) * CertifiedNumerics.logOnePlusRatio r +
        Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
          (2 / 25 : ℝ) * r ^ 2) +
        (-finalU r / 2 - (7 / 20 : ℝ) * r -
          (13 / 100 : ℝ) * r ^ 2)) := by
    rw [hw.base]
    exact (hEntropy.add hCorr).add hTail
  have hOnePlusT : d.onePlusT.Contains (1 + finalSmallParameter r) := by
    rw [hw.onePlusT]
    exact hone.add hparameter
  have hLogRatio : d.logRatio.Contains (Real.log (finalSmallRatio r)) := by
    rw [hw.logRatio]
    exact FixedPointInterval.Sound.contains_log_of_safe hratio hc.logRatioSafe
  have hLogOnePlusT : d.logOnePlusT.Contains
      (Real.log (1 + finalSmallParameter r)) := by
    rw [hw.logOnePlusT]
    exact FixedPointInterval.Sound.contains_log_of_safe hOnePlusT hc.logOnePlusTSafe
  have hPrelimR := preliminaryR_contains hparameter hParameterNonneg
  have hExpR : d.expR.Contains
      (Real.exp (-finalSmallParameter r) *
        preliminaryFrontierR (finalSmallParameter r)) := by
    rw [hw.expR]
    exact hexpNegT.mul hPrelimR
  have hLogAWithoutR : d.logAWithoutR.Contains
      (Real.log (finalSmallRatio r) - Real.log (1 + finalSmallParameter r) -
        Real.exp (-finalSmallParameter r) *
          preliminaryFrontierR (finalSmallParameter r)) := by
    rw [hw.logAWithoutR]
    exact sub_contains (sub_contains hLogRatio hLogOnePlusT) hExpR
  have hSlack0 := hBase.add (hLogAWithoutR.divNat (by norm_num : 0 < 2))
  have hSlack : d.slack.Contains (finalSmallNormalizedSlack r) := by
    rw [hw.slack]
    convert hSlack0 using 1 <;> simp only [finalSmallNormalizedSlack] <;> ring
  have hPrelimS := preliminaryS_contains hparameter hParameterNonneg
  have hLogB : d.logB.Contains
      (-Real.log (1 + finalSmallParameter r) +
        Real.exp (-finalSmallParameter r) *
          preliminaryFrontierS (finalSmallParameter r)) := by
    rw [hw.logB]
    exact hLogOnePlusT.neg.add (hexpNegT.mul hPrelimS)
  have hUNonneg : 0 ≤ d.common.u.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hCommonChecks.uNonneg
  have hRU : (mulNonneg d.input d.common.u).Contains (r * finalU r) :=
    hr.mulNonneg hCommon.u hInputNonneg hUNonneg
  have hCoordinate : d.coordinateGap.Contains
      (r * finalU r - Real.log (1 + finalSmallParameter r) +
        Real.exp (-finalSmallParameter r) *
          preliminaryFrontierS (finalSmallParameter r)) := by
    rw [hw.coordinateGap]
    convert hRU.add hLogB using 1 <;> ring
  exact ⟨hparameter, hCoordinate, hSlack, hratioPos⟩

end

end RamseyLean.FinalCertificate

