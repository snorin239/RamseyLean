import RamseyLean.Numerics.FinalCertificateBranchHelpers

/-! Direct-entropy and hyperbolic-middle certificates for the final descent. -/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open FixedPointInterval

noncomputable section

structure EntropyData where
  input : Interval
  onePlus : Interval
  logOnePlus : Interval
  logInput : Interval
  invInput : Interval
  entropy : Interval

def entropyData (r : Interval) : EntropyData :=
  let onePlus := add (point scale) r
  let logOnePlus := log 16 onePlus
  let logInput := log 16 r
  let invInput := inv r
  let entropy := mul onePlus (mul logOnePlus invInput)
  ⟨r, onePlus, logOnePlus, logInput, invInput, entropy⟩

def EntropyData.safe (d : EntropyData) : Bool :=
  positive d.input && logSafe 16 d.input && logSafe 16 d.onePlus

structure EntropyData.Checks (d : EntropyData) : Prop where
  inputPositive : positive d.input = true
  logInputSafe : logSafe 16 d.input = true
  logOnePlusSafe : logSafe 16 d.onePlus = true

theorem EntropyData.checks_of_safe {d : EntropyData} (h : d.safe = true) : d.Checks := by
  simp only [EntropyData.safe, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

structure EntropyData.WellFormed (d : EntropyData) : Prop where
  onePlus : d.onePlus = add (point scale) d.input
  logOnePlus : d.logOnePlus = log 16 d.onePlus
  logInput : d.logInput = log 16 d.input
  invInput : d.invInput = inv d.input
  entropy : d.entropy = mul d.onePlus (mul d.logOnePlus d.invInput)

theorem entropyData_wellFormed (I : Interval) : (entropyData I).WellFormed := by
  constructor <;> rfl

structure EntropyData.Sound (d : EntropyData) (r : ℝ) : Prop where
  logInput : d.logInput.Contains (Real.log r)
  entropy : d.entropy.Contains ((1 + r) * (Real.log (1 + r) / r))

theorem EntropyData.sound {d : EntropyData} {r : ℝ}
    (hw : d.WellFormed) (hc : d.Checks) (hr : d.input.Contains r) : d.Sound r := by
  have hpos : 0 < d.input.lo := by
    simpa only [positive, decide_eq_true_eq] using hc.inputPositive
  have hone : (point scale).Contains (1 : ℝ) := by
    have h := Interval.contains_point scale
    convert h using 1
    norm_num [FixedPointInterval.value, scale]
  have hOnePlus : d.onePlus.Contains (1 + r) := by
    rw [hw.onePlus]
    exact hone.add hr
  have hLogOnePlus : d.logOnePlus.Contains (Real.log (1 + r)) := by
    rw [hw.logOnePlus]
    exact FixedPointInterval.Sound.contains_log_of_safe hOnePlus hc.logOnePlusSafe
  have hLogInput : d.logInput.Contains (Real.log r) := by
    rw [hw.logInput]
    exact FixedPointInterval.Sound.contains_log_of_safe hr hc.logInputSafe
  have hInv : d.invInput.Contains r⁻¹ := by
    rw [hw.invInput]
    exact hr.inv hpos
  have hEntropy : d.entropy.Contains ((1 + r) * (Real.log (1 + r) / r)) := by
    rw [hw.entropy]
    simpa only [div_eq_mul_inv] using hOnePlus.mul (hLogOnePlus.mul hInv)
  exact ⟨hLogInput, hEntropy⟩

structure FOneData where
  two : Interval
  logTwo : Interval
  expNegOne : Interval
  value : Interval

def fOneData : FOneData :=
  let two := rationalInterval 2 1
  let logTwo := log 16 two
  let expNegOne := exp 12 (rationalInterval (-1) 1)
  let value := add (mulNat logTwo 2)
    (mul (rationalInterval (-19) 200) expNegOne)
  ⟨two, logTwo, expNegOne, value⟩

def FOneData.safe (d : FOneData) : Bool :=
  logSafe 16 d.two && expSafe 12 (rationalInterval (-1) 1)

structure FOneData.Checks (d : FOneData) : Prop where
  logSafe : logSafe 16 d.two = true
  expSafe : expSafe 12 (rationalInterval (-1) 1) = true

theorem FOneData.checks_of_safe {d : FOneData} (h : d.safe = true) : d.Checks := by
  simp only [FOneData.safe, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

structure FOneData.WellFormed (d : FOneData) : Prop where
  two : d.two = rationalInterval 2 1
  logTwo : d.logTwo = log 16 d.two
  expNegOne : d.expNegOne = exp 12 (rationalInterval (-1) 1)
  value : d.value = add (mulNat d.logTwo 2)
    (mul (rationalInterval (-19) 200) d.expNegOne)

theorem fOneData_wellFormed : fOneData.WellFormed := by
  constructor <;> rfl

theorem FOneData.sound {d : FOneData} (hw : d.WellFormed) (hc : d.Checks) :
    d.value.Contains (F preliminaryB 1) := by
  have htwo : d.two.Contains (2 : ℝ) := by
    rw [hw.two]
    convert rationalInterval_contains 2 (q := 1) (by norm_num) using 1 <;> norm_num
  have hlog : d.logTwo.Contains (Real.log 2) := by
    rw [hw.logTwo]
    exact FixedPointInterval.Sound.contains_log_of_safe htwo hc.logSafe
  have hnegOne : (rationalInterval (-1) 1).Contains (-(1 : ℝ)) := by
    convert rationalInterval_contains (-1) (q := 1) (by norm_num) using 1 <;> norm_num
  have hexp : d.expNegOne.Contains (Real.exp (-(1 : ℝ))) := by
    rw [hw.expNegOne]
    exact FixedPointInterval.Sound.contains_exp_of_safe hnegOne hc.expSafe
  have hn19 : (rationalInterval (-19) 200).Contains (-(19 / 200 : ℝ)) := by
    convert rationalInterval_contains (-19) (q := 200) (by norm_num) using 1 <;>
      norm_num
  have h := (hlog.mulNat (k := 2)).add (hn19.mul hexp)
  rw [hw.value]
  convert h using 1 <;>
    simp only [F, entropy, g, gPoly, preliminaryB, Real.log_one] <;> ring

structure MiddleData where
  input : Interval
  common : CommonData
  entropy : EntropyData
  fOne : FOneData
  oneMinusR : Interval
  uTerm : Interval
  tail : Interval
  corr : Interval
  logTerm : Interval
  fOneTerm : Interval
  slack : Interval

def middleData (r : Interval) : MiddleData :=
  let c := commonData r
  let ent := entropyData r
  let fOne := fOneData
  let oneMinusR := sub (point scale) r
  let uTerm := neg (divNat (mul oneMinusR c.u) 2)
  let tail := add (add uTerm (mul (rationalInterval (-7) 20) r))
    (mul (rationalInterval (-13) 100) c.r2)
  let corr := correction r c.r2 c.expNegR
  let logTerm := neg (divNat ent.logInput 2)
  let fOneTerm := neg (divNat fOne.value 2)
  let slack := add (add (add (add ent.entropy corr) tail) logTerm) fOneTerm
  ⟨r, c, ent, fOne, oneMinusR, uTerm, tail, corr, logTerm, fOneTerm, slack⟩

def MiddleData.safe (d : MiddleData) : Bool :=
  d.common.safe && d.entropy.safe && d.fOne.safe

structure MiddleData.Checks (d : MiddleData) : Prop where
  commonSafe : d.common.safe = true
  entropySafe : d.entropy.safe = true
  fOneSafe : d.fOne.safe = true

theorem MiddleData.checks_of_safe {d : MiddleData} (h : d.safe = true) : d.Checks := by
  simp only [MiddleData.safe, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

structure MiddleData.WellFormed (d : MiddleData) : Prop where
  common : d.common = commonData d.input
  entropy : d.entropy = entropyData d.input
  fOne : d.fOne = fOneData
  oneMinusR : d.oneMinusR = sub (point scale) d.input
  uTerm : d.uTerm = neg (divNat (mul d.oneMinusR d.common.u) 2)
  tail : d.tail = add (add d.uTerm (mul (rationalInterval (-7) 20) d.input))
    (mul (rationalInterval (-13) 100) d.common.r2)
  corr : d.corr = correction d.input d.common.r2 d.common.expNegR
  logTerm : d.logTerm = neg (divNat d.entropy.logInput 2)
  fOneTerm : d.fOneTerm = neg (divNat d.fOne.value 2)
  slack : d.slack = add (add (add (add d.entropy.entropy d.corr) d.tail)
    d.logTerm) d.fOneTerm

theorem middleData_wellFormed (I : Interval) : (middleData I).WellFormed := by
  constructor <;> rfl

theorem MiddleData.sound {d : MiddleData} {r : ℝ}
    (hw : d.WellFormed) (hc : d.Checks) (hr : d.input.Contains r)
    (hrpos : 0 < r) : d.slack.Contains (finalMiddleNormalizedSlack r) := by
  have hCommonWF : d.common.WellFormed := by rw [hw.common]; exact commonData_wellFormed _
  have hCommonChecks := CommonData.checks_of_safe hc.commonSafe
  have hCommonInput : d.common.input = d.input := by rw [hw.common]; rfl
  have hrCommon : d.common.input.Contains r := by simpa only [hCommonInput] using hr
  have hCommon := CommonData.sound hCommonWF hCommonChecks hrCommon hrpos
  have hEntropyWF : d.entropy.WellFormed := by rw [hw.entropy]; exact entropyData_wellFormed _
  have hEntropyChecks := EntropyData.checks_of_safe hc.entropySafe
  have hEntropyInput : d.entropy.input = d.input := by rw [hw.entropy]; rfl
  have hrEntropy : d.entropy.input.Contains r := by simpa only [hEntropyInput] using hr
  have hEntropy := EntropyData.sound hEntropyWF hEntropyChecks hrEntropy
  have hFOneWF : d.fOne.WellFormed := by rw [hw.fOne]; exact fOneData_wellFormed
  have hFOneChecks := FOneData.checks_of_safe hc.fOneSafe
  have hFOne := FOneData.sound hFOneWF hFOneChecks
  have hone : (point scale).Contains (1 : ℝ) := by
    have h := Interval.contains_point scale
    convert h using 1
    norm_num [FixedPointInterval.value, scale]
  have hOneMinusR : d.oneMinusR.Contains (1 - r) := by
    rw [hw.oneMinusR]
    simpa only [sub, sub_eq_add_neg] using hone.add hr.neg
  have hUTerm : d.uTerm.Contains (-((1 - r) * finalU r) / 2) := by
    rw [hw.uTerm]
    convert ((hOneMinusR.mul hCommon.u).divNat (by norm_num : 0 < 2)).neg using 1 <;>
      ring
  have hn7 : (rationalInterval (-7) 20).Contains (-(7 / 20 : ℝ)) := by
    convert rationalInterval_contains (-7) (q := 20) (by norm_num) using 1 <;> norm_num
  have hn13 : (rationalInterval (-13) 100).Contains (-(13 / 100 : ℝ)) := by
    convert rationalInterval_contains (-13) (q := 100) (by norm_num) using 1 <;> norm_num
  have hTail : d.tail.Contains
      (-((1 - r) * finalU r) / 2 - (7 / 20 : ℝ) * r -
        (13 / 100 : ℝ) * r ^ 2) := by
    rw [hw.tail]
    convert (hUTerm.add (hn7.mul hr)).add (hn13.mul hCommon.r2) using 1 <;> ring
  have hCorr := correction_contains hr hCommon.r2 hCommon.expNegR
  rw [← hw.corr] at hCorr
  have hLogTerm : d.logTerm.Contains (-Real.log r / 2) := by
    rw [hw.logTerm]
    convert (hEntropy.logInput.divNat (by norm_num : 0 < 2)).neg using 1 <;> ring
  have hFOneTerm : d.fOneTerm.Contains (-F preliminaryB 1 / 2) := by
    rw [hw.fOneTerm]
    convert (hFOne.divNat (by norm_num : 0 < 2)).neg using 1 <;> ring
  rw [hw.slack]
  have h := (((hEntropy.entropy.add hCorr).add hTail).add hLogTerm).add hFOneTerm
  convert h using 1 <;> simp only [finalMiddleNormalizedSlack] <;> ring

end

end RamseyLean.FinalCertificate
