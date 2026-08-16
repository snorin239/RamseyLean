import RamseyLean.Numerics.FinalCertificateMiddle

/-! The t=1 cap and three large-r quartic branch certificates. -/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

noncomputable section

def LargeBand.Matches (band : LargeBand) (r : ℝ) : Prop :=
  match band with
  | .cutNineTwentieths => r ≤ 9 / 20
  | .nineTwentiethsThreeFifths => 9 / 20 < r ∧ r ≤ 3 / 5
  | .threeFifthsOne => 3 / 5 < r

def largeParameterValue (band : LargeBand) (r : ℝ) : ℝ :=
  match band with
  | .cutNineTwentieths =>
      finalQuartic (10036 / 10000) (-(4315 / 10000)) (1157 / 10000)
        (-(101 / 10000)) (-(23 / 10000)) ((100 / 9) * (r - 9 / 25))
  | .nineTwentiethsThreeFifths =>
      finalQuartic (6755 / 10000) (-(3986 / 10000)) (2018 / 10000)
        (-(717 / 10000)) (136 / 10000) ((20 / 3) * (r - 9 / 20))
  | .threeFifthsOne =>
      finalQuartic (4206 / 10000) (-(4085 / 10000)) (4170 / 10000)
        (-(2475 / 10000)) (702 / 10000) ((5 / 2) * (r - 3 / 5))

theorem largeParameter_contains (band : LargeBand) {I : Interval} {r : ℝ}
    (hr : I.Contains r) :
    (largeParameter band I).Contains (largeParameterValue band r) := by
  have h9_25 : (rationalInterval 9 25).Contains (9 / 25 : ℝ) :=
    rationalInterval_contains 9 (q := 25) (by norm_num)
  have h9_20 : (rationalInterval 9 20).Contains (9 / 20 : ℝ) :=
    rationalInterval_contains 9 (q := 20) (by norm_num)
  have h3_5 : (rationalInterval 3 5).Contains (3 / 5 : ℝ) :=
    rationalInterval_contains 3 (q := 5) (by norm_num)
  cases band with
  | cutNineTwentieths =>
      apply quartic_contains
      · exact rationalInterval_contains 10036 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-4315) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · exact rationalInterval_contains 1157 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-101) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · convert rationalInterval_contains (-23) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · exact (rationalInterval_contains 100 (q := 9) (by norm_num)).mul
          (sub_contains hr h9_25)
  | nineTwentiethsThreeFifths =>
      apply quartic_contains
      · exact rationalInterval_contains 6755 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-3986) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · exact rationalInterval_contains 2018 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-717) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · exact rationalInterval_contains 136 (q := 10000) (by norm_num)
      · exact (rationalInterval_contains 20 (q := 3) (by norm_num)).mul
          (sub_contains hr h9_20)
  | threeFifthsOne =>
      apply quartic_contains
      · exact rationalInterval_contains 4206 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-4085) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · exact rationalInterval_contains 4170 (q := 10000) (by norm_num)
      · convert rationalInterval_contains (-2475) (q := 10000) (by norm_num) using 1 <;>
          norm_num
      · exact rationalInterval_contains 702 (q := 10000) (by norm_num)
      · exact (rationalInterval_contains 5 (q := 2) (by norm_num)).mul
          (sub_contains hr h3_5)

theorem largeParameterValue_eq_final {band : LargeBand} {r : ℝ}
    (h : band.Matches r) : largeParameterValue band r = finalLargeParameter r := by
  cases band with
  | cutNineTwentieths =>
      change r ≤ (9 / 20 : ℝ) at h
      rw [finalLargeParameter, if_pos h]
      rfl
  | nineTwentiethsThreeFifths =>
      change (9 / 20 : ℝ) < r ∧ r ≤ 3 / 5 at h
      have hn : ¬ r ≤ 9 / 20 := not_le.mpr h.1
      rw [finalLargeParameter, if_neg hn, if_pos h.2]
      rfl
  | threeFifthsOne =>
      change (3 / 5 : ℝ) < r at h
      have hcut : (9 / 20 : ℝ) < 3 / 5 := by norm_num
      have hn1 : ¬ r ≤ 9 / 20 := not_le.mpr (hcut.trans h)
      have hn2 : ¬ r ≤ 3 / 5 := not_le.mpr h
      rw [finalLargeParameter, if_neg hn1, if_neg hn2]
      rfl

def largeNormalizedSlackAt (r parameter : ℝ) : ℝ :=
  (1 + r) * (Real.log (1 + r) / r) +
    Real.exp (-r) * (-(1 / 4 : ℝ) + (3 / 100 : ℝ) * r +
      (2 / 25 : ℝ) * r ^ 2) -
    finalU r / 2 - (7 / 20 : ℝ) * r - (13 / 100 : ℝ) * r ^ 2 -
    Real.log r / 2 +
    (-Real.log (1 + parameter) + Real.exp (-parameter) *
      preliminaryFrontierS parameter) / 2

theorem largeNormalizedSlackAt_one (r : ℝ) :
    largeNormalizedSlackAt r 1 = finalLargeCapNormalizedSlack r := by
  unfold largeNormalizedSlackAt finalLargeCapNormalizedSlack
  ring

theorem largeNormalizedSlackAt_final (r : ℝ) :
    largeNormalizedSlackAt r (finalLargeParameter r) =
      finalLargeNormalizedSlack r := by
  rfl

structure LargeData where
  input : Interval
  parameter : Interval
  common : CommonData
  entropy : EntropyData
  negT : Interval
  expNegT : Interval
  onePlusT : Interval
  logT : Interval
  logOnePlusT : Interval
  expR : Interval
  logA : Interval
  logB : Interval
  corr : Interval
  tail : Interval
  logTerm : Interval
  base : Interval
  slack : Interval
  coordinateGap : Interval

def largeData (r parameter : Interval) : LargeData :=
  let c := commonData r
  let ent := entropyData r
  let negT := neg parameter
  let expNegT := exp 12 negT
  let onePlusT := add (point scale) parameter
  let logT := log 16 parameter
  let logOnePlusT := log 16 onePlusT
  let expR := mul expNegT (preliminaryR parameter)
  let logA := sub (sub logT logOnePlusT) expR
  let logB := add (neg logOnePlusT)
    (mul expNegT (preliminaryS parameter))
  let corr := correction r c.r2 c.expNegR
  let tail := commonTail r c.r2 c.u
  let logTerm := neg (divNat ent.logInput 2)
  let base := add (add (add ent.entropy corr) tail) logTerm
  let slack := add base (divNat logB 2)
  let coordinateGap := add (mulNonneg r c.u) logA
  ⟨r, parameter, c, ent, negT, expNegT, onePlusT, logT, logOnePlusT,
    expR, logA, logB, corr, tail, logTerm, base, slack, coordinateGap⟩

def LargeData.safe (d : LargeData) : Bool :=
  d.common.safe && d.entropy.safe && nonneg d.parameter &&
  positive d.parameter && expSafe 12 d.negT && logSafe 16 d.parameter &&
  logSafe 16 d.onePlusT && decide (d.parameter.hi ≤ scale)

structure LargeData.Checks (d : LargeData) : Prop where
  commonSafe : d.common.safe = true
  entropySafe : d.entropy.safe = true
  parameterNonneg : nonneg d.parameter = true
  parameterPositive : positive d.parameter = true
  expNegTSafe : expSafe 12 d.negT = true
  logParameterSafe : logSafe 16 d.parameter = true
  logOnePlusTSafe : logSafe 16 d.onePlusT = true
  parameterUpper : d.parameter.hi ≤ scale

theorem LargeData.checks_of_safe {d : LargeData} (h : d.safe = true) : d.Checks := by
  simp only [LargeData.safe, Bool.and_eq_true, decide_eq_true_eq] at h
  constructor <;> aesop

structure LargeData.WellFormed (d : LargeData) : Prop where
  common : d.common = commonData d.input
  entropy : d.entropy = entropyData d.input
  negT : d.negT = neg d.parameter
  expNegT : d.expNegT = exp 12 d.negT
  onePlusT : d.onePlusT = add (point scale) d.parameter
  logT : d.logT = log 16 d.parameter
  logOnePlusT : d.logOnePlusT = log 16 d.onePlusT
  expR : d.expR = mul d.expNegT (preliminaryR d.parameter)
  logA : d.logA = sub (sub d.logT d.logOnePlusT) d.expR
  logB : d.logB = add (neg d.logOnePlusT)
    (mul d.expNegT (preliminaryS d.parameter))
  corr : d.corr = correction d.input d.common.r2 d.common.expNegR
  tail : d.tail = commonTail d.input d.common.r2 d.common.u
  logTerm : d.logTerm = neg (divNat d.entropy.logInput 2)
  base : d.base = add (add (add d.entropy.entropy d.corr) d.tail) d.logTerm
  slack : d.slack = add d.base (divNat d.logB 2)
  coordinateGap : d.coordinateGap = add (mulNonneg d.input d.common.u) d.logA

theorem largeData_wellFormed (I T : Interval) : (largeData I T).WellFormed := by
  constructor <;> rfl

structure LargeData.Sound (d : LargeData) (r parameter : ℝ) : Prop where
  coordinateGap : d.coordinateGap.Contains
    (r * finalU r + Real.log parameter - Real.log (1 + parameter) -
      Real.exp (-parameter) * preliminaryFrontierR parameter)
  slack : d.slack.Contains (largeNormalizedSlackAt r parameter)
  parameterPos : 0 < parameter

theorem LargeData.sound {d : LargeData} {r parameter : ℝ}
    (hw : d.WellFormed) (hc : d.Checks) (hr : d.input.Contains r)
    (ht : d.parameter.Contains parameter) (hrpos : 0 < r) :
    d.Sound r parameter := by
  have hParameterNonneg : 0 ≤ d.parameter.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.parameterNonneg
  have hParameterPositive : 0 < d.parameter.lo := by
    simpa only [positive, decide_eq_true_eq] using hc.parameterPositive
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
  have hEntropyWF : d.entropy.WellFormed := by rw [hw.entropy]; exact entropyData_wellFormed _
  have hEntropyChecks := EntropyData.checks_of_safe hc.entropySafe
  have hEntropyInput : d.entropy.input = d.input := by rw [hw.entropy]; rfl
  have hrEntropy : d.entropy.input.Contains r := by simpa only [hEntropyInput] using hr
  have hEntropy := EntropyData.sound hEntropyWF hEntropyChecks hrEntropy
  have htpos : 0 < parameter := by
    have hv : 0 < FixedPointInterval.value d.parameter.lo := by
      unfold FixedPointInterval.value
      exact div_pos (by exact_mod_cast hParameterPositive) scale_pos_real
    exact hv.trans_le ht.1
  have hone : (point scale).Contains (1 : ℝ) := by
    have h := Interval.contains_point scale
    convert h using 1
    norm_num [FixedPointInterval.value, scale]
  have hnegT : d.negT.Contains (-parameter) := by rw [hw.negT]; exact ht.neg
  have hexpNegT : d.expNegT.Contains (Real.exp (-parameter)) := by
    rw [hw.expNegT]
    exact FixedPointInterval.Sound.contains_exp_of_safe hnegT hc.expNegTSafe
  have hOnePlusT : d.onePlusT.Contains (1 + parameter) := by
    rw [hw.onePlusT]
    exact hone.add ht
  have hLogT : d.logT.Contains (Real.log parameter) := by
    rw [hw.logT]
    exact FixedPointInterval.Sound.contains_log_of_safe ht hc.logParameterSafe
  have hLogOnePlusT : d.logOnePlusT.Contains (Real.log (1 + parameter)) := by
    rw [hw.logOnePlusT]
    exact FixedPointInterval.Sound.contains_log_of_safe hOnePlusT hc.logOnePlusTSafe
  have hPrelimR := preliminaryR_contains ht hParameterNonneg
  have hExpR : d.expR.Contains
      (Real.exp (-parameter) * preliminaryFrontierR parameter) := by
    rw [hw.expR]
    exact hexpNegT.mul hPrelimR
  have hLogA : d.logA.Contains
      (Real.log parameter - Real.log (1 + parameter) -
        Real.exp (-parameter) * preliminaryFrontierR parameter) := by
    rw [hw.logA]
    exact sub_contains (sub_contains hLogT hLogOnePlusT) hExpR
  have hPrelimS := preliminaryS_contains ht hParameterNonneg
  have hLogB : d.logB.Contains
      (-Real.log (1 + parameter) +
        Real.exp (-parameter) * preliminaryFrontierS parameter) := by
    rw [hw.logB]
    exact hLogOnePlusT.neg.add (hexpNegT.mul hPrelimS)
  have hCorr := correction_contains hr hCommon.r2 hCommon.expNegR
  rw [← hw.corr] at hCorr
  have hTail := commonTail_contains hr hCommon.r2 hCommon.u
  rw [← hw.tail] at hTail
  have hLogTerm : d.logTerm.Contains (-Real.log r / 2) := by
    rw [hw.logTerm]
    convert (hEntropy.logInput.divNat (by norm_num : 0 < 2)).neg using 1 <;> ring
  have hBase := ((hEntropy.entropy.add hCorr).add hTail).add hLogTerm
  have hSlack0 := hBase.add (hLogB.divNat (by norm_num : 0 < 2))
  have hSlack : d.slack.Contains (largeNormalizedSlackAt r parameter) := by
    rw [hw.slack, hw.base]
    convert hSlack0 using 1 <;> simp only [largeNormalizedSlackAt] <;> ring
  have hRU := hr.mulNonneg hCommon.u hInputNonneg hUNonneg
  have hCoordinate : d.coordinateGap.Contains
      (r * finalU r + Real.log parameter - Real.log (1 + parameter) -
        Real.exp (-parameter) * preliminaryFrontierR parameter) := by
    rw [hw.coordinateGap]
    convert hRU.add hLogA using 1 <;> ring
  exact ⟨hCoordinate, hSlack, htpos⟩

end

end RamseyLean.FinalCertificate

