import RamseyLean.Numerics.FinalCertificateBranchHelpers

/-! Smooth log-gap certificates bracketing the two t=1 frontier crossings. -/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open FixedPointInterval

noncomputable section

structure CrossingData where
  input : Interval
  common : CommonData
  parameter : Interval
  negT : Interval
  expNegT : Interval
  onePlusT : Interval
  logT : Interval
  logOnePlusT : Interval
  expR : Interval
  logA : Interval
  logB : Interval
  rU : Interval
  aGap : Interval
  bGap : Interval

def crossingData (r : Interval) : CrossingData :=
  let c := commonData r
  let parameter := point scale
  let negT := neg parameter
  let expNegT := exp 12 negT
  let onePlusT := add (point scale) parameter
  let logT := log 16 parameter
  let logOnePlusT := log 16 onePlusT
  let expR := mul expNegT (preliminaryR parameter)
  let logA := sub (sub logT logOnePlusT) expR
  let logB := add (neg logOnePlusT)
    (mul expNegT (preliminaryS parameter))
  let rU := mulNonneg r c.u
  let aGap := add rU logA
  let bGap := add rU logB
  ⟨r, c, parameter, negT, expNegT, onePlusT, logT, logOnePlusT,
    expR, logA, logB, rU, aGap, bGap⟩

def CrossingData.safe (d : CrossingData) : Bool :=
  d.common.safe && expSafe 12 d.negT && logSafe 16 d.parameter &&
    logSafe 16 d.onePlusT

structure CrossingData.Checks (d : CrossingData) : Prop where
  commonSafe : d.common.safe = true
  expSafe : expSafe 12 d.negT = true
  logParameterSafe : logSafe 16 d.parameter = true
  logOnePlusSafe : logSafe 16 d.onePlusT = true

theorem CrossingData.checks_of_safe {d : CrossingData} (h : d.safe = true) : d.Checks := by
  simp only [CrossingData.safe, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

structure CrossingData.WellFormed (d : CrossingData) : Prop where
  common : d.common = commonData d.input
  parameter : d.parameter = point scale
  negT : d.negT = neg d.parameter
  expNegT : d.expNegT = exp 12 d.negT
  onePlusT : d.onePlusT = add (point scale) d.parameter
  logT : d.logT = log 16 d.parameter
  logOnePlusT : d.logOnePlusT = log 16 d.onePlusT
  expR : d.expR = mul d.expNegT (preliminaryR d.parameter)
  logA : d.logA = sub (sub d.logT d.logOnePlusT) d.expR
  logB : d.logB = add (neg d.logOnePlusT)
    (mul d.expNegT (preliminaryS d.parameter))
  rU : d.rU = mulNonneg d.input d.common.u
  aGap : d.aGap = add d.rU d.logA
  bGap : d.bGap = add d.rU d.logB

theorem crossingData_wellFormed (I : Interval) : (crossingData I).WellFormed := by
  constructor <;> rfl

structure CrossingData.Sound (d : CrossingData) (r : ℝ) : Prop where
  aGap : d.aGap.Contains
    (r * finalU r - Real.log (2 : ℝ) -
      Real.exp (-(1 : ℝ)) * preliminaryFrontierR 1)
  bGap : d.bGap.Contains
    (r * finalU r - Real.log (2 : ℝ) +
      Real.exp (-(1 : ℝ)) * preliminaryFrontierS 1)

theorem CrossingData.sound {d : CrossingData} {r : ℝ}
    (hw : d.WellFormed) (hc : d.Checks) (hr : d.input.Contains r)
    (hrpos : 0 < r) : d.Sound r := by
  have hCommonWF : d.common.WellFormed := by rw [hw.common]; exact commonData_wellFormed _
  have hCommonChecks := CommonData.checks_of_safe hc.commonSafe
  have hCommonInput : d.common.input = d.input := by rw [hw.common]; rfl
  have hrCommon : d.common.input.Contains r := by simpa only [hCommonInput] using hr
  have hCommon := CommonData.sound hCommonWF hCommonChecks hrCommon hrpos
  have hInputNonneg : 0 ≤ d.input.lo := by
    rw [← hCommonInput]
    simpa only [nonneg, decide_eq_true_eq] using hCommonChecks.inputNonneg
  have hUNonneg : 0 ≤ d.common.u.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hCommonChecks.uNonneg
  have hone : (point scale).Contains (1 : ℝ) := by
    have h := Interval.contains_point scale
    convert h using 1
    norm_num [FixedPointInterval.value, scale]
  have ht : d.parameter.Contains (1 : ℝ) := by rw [hw.parameter]; exact hone
  have htNonneg : 0 ≤ d.parameter.lo := by rw [hw.parameter]; norm_num [point, scale]
  have hnegT : d.negT.Contains (-(1 : ℝ)) := by rw [hw.negT]; exact ht.neg
  have hexp : d.expNegT.Contains (Real.exp (-(1 : ℝ))) := by
    rw [hw.expNegT]
    exact FixedPointInterval.Sound.contains_exp_of_safe hnegT hc.expSafe
  have hOnePlus : d.onePlusT.Contains (2 : ℝ) := by
    rw [hw.onePlusT]
    convert hone.add ht using 1 <;> ring
  have hLogT : d.logT.Contains (Real.log (1 : ℝ)) := by
    rw [hw.logT]
    exact FixedPointInterval.Sound.contains_log_of_safe ht hc.logParameterSafe
  have hLogOnePlus : d.logOnePlusT.Contains (Real.log (2 : ℝ)) := by
    rw [hw.logOnePlusT]
    exact FixedPointInterval.Sound.contains_log_of_safe hOnePlus hc.logOnePlusSafe
  have hPrelimR := preliminaryR_contains ht htNonneg
  have hExpR : d.expR.Contains
      (Real.exp (-(1 : ℝ)) * preliminaryFrontierR 1) := by
    rw [hw.expR]
    exact hexp.mul hPrelimR
  have hLogA : d.logA.Contains
      (-Real.log (2 : ℝ) - Real.exp (-(1 : ℝ)) *
        preliminaryFrontierR 1) := by
    rw [hw.logA]
    have h := sub_contains (sub_contains hLogT hLogOnePlus) hExpR
    simpa only [Real.log_one, zero_sub] using h
  have hPrelimS := preliminaryS_contains ht htNonneg
  have hLogB : d.logB.Contains
      (-Real.log (2 : ℝ) + Real.exp (-(1 : ℝ)) *
        preliminaryFrontierS 1) := by
    rw [hw.logB]
    exact hLogOnePlus.neg.add (hexp.mul hPrelimS)
  have hRU : d.rU.Contains (r * finalU r) := by
    rw [hw.rU]
    exact hr.mulNonneg hCommon.u hInputNonneg hUNonneg
  constructor
  · rw [hw.aGap]
    convert hRU.add hLogA using 1 <;> ring
  · rw [hw.bGap]
    convert hRU.add hLogB using 1 <;> ring

end

end RamseyLean.FinalCertificate
