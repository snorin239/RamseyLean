import RamseyLean.Numerics.FinalCertificate

/-!
# Soundness and certificates for the final numerical descent

This module gives the staged fixed-point computation in
`RamseyLean.Numerics.FinalCertificate` a named DAG interface.  Separating the
Boolean computation from its real semantics prevents proof simplification from
unfolding the large closed integer terms.  Reducibility is enabled only around
the eventual closed certificate checks.
-/

set_option autoImplicit false

namespace RamseyLean.FinalCertificate

open Set
open FixedPointInterval

noncomputable section

/-! ## Basic cast soundness -/

/-- A rational singleton interval contains the corresponding real number. -/
theorem rationalInterval_contains (p : ℤ) {q : ℕ} (hq : 0 < q) :
    (rationalInterval p q).Contains ((p : ℝ) / (q : ℝ)) := by
  have h := (Interval.contains_point (p * scale)).divNat hq
  unfold rationalInterval
  convert h using 1
  unfold FixedPointInterval.value
  push_cast
  field_simp [FixedPointInterval.scale_pos_real.ne', (by positivity : (q : ℝ) ≠ 0)]

theorem sub_contains {I J : Interval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (sub I J).Contains (x - y) := by
  simpa only [sub, sub_eq_add_neg] using hx.add hy.neg

theorem quartic_contains {c₀ c₁ c₂ c₃ c₄ u : Interval}
    {a₀ a₁ a₂ a₃ a₄ x : ℝ}
    (h₀ : c₀.Contains a₀) (h₁ : c₁.Contains a₁)
    (h₂ : c₂.Contains a₂) (h₃ : c₃.Contains a₃)
    (h₄ : c₄.Contains a₄) (hu : u.Contains x) :
    (quartic c₀ c₁ c₂ c₃ c₄ u).Contains
      (finalQuartic a₀ a₁ a₂ a₃ a₄ x) := by
  exact h₀.add (hu.mul (h₁.add (hu.mul
    (h₂.add (hu.mul (h₃.add (hu.mul h₄)))))))

/-! ## Named common DAG -/

/-- Named intermediate intervals shared by every final branch. -/
structure CommonData where
  input : Interval
  r2 : Interval
  r3 : Interval
  remainder : Interval
  negR : Interval
  expNegR : Interval
  mExponent : Interval
  mRatio : Interval
  m : Interval
  aInner : Interval
  aExp : Interval
  onePlusR : Interval
  invOnePlusR : Interval
  aRatio : Interval
  a : Interval
  tm : Interval
  ta : Interval
  oneMinusM : Interval
  invOneMinusM : Interval
  uLeft : Interval
  uRight0 : Interval
  uRight : Interval
  u : Interval

/-- Evaluate the shared final-descent DAG. -/
def commonData (r : Interval) : CommonData :=
  let r2 := mulNonneg r r
  let r3 := mulNonneg r2 r
  let remainder :=
    add (add (add (rationalInterval (-1) 4)
      (mul (rationalInterval 31 100) r))
      (mul (rationalInterval 21 100) r2))
      (mul (rationalInterval (-2) 25) r3)
  let negR := neg r
  let expNegR := exp 12 negR
  let mExponent := add (mul (rationalInterval (-7) 10) r)
    (mul (rationalInterval (-13) 50) r2)
  let mRatio := exp 12 mExponent
  let m := mulNonneg r mRatio
  let aInner := neg (mul expNegR remainder)
  let aExp := exp 12 aInner
  let onePlusR := add (point scale) r
  let invOnePlusR := inv onePlusR
  let aRatio := mulNonneg aExp invOnePlusR
  let a := mulNonneg r aRatio
  let tm := t 16 m
  let ta := t 16 a
  let oneMinusM := sub (point scale) m
  let invOneMinusM := inv oneMinusM
  let uLeft := mulNonneg mRatio tm
  let uRight0 := mulNonneg aRatio ta
  let uRight := mulNonneg uRight0 invOneMinusM
  let u := add uLeft uRight
  ⟨r, r2, r3, remainder, negR, expNegR, mExponent, mRatio, m,
    aInner, aExp, onePlusR, invOnePlusR, aRatio, a, tm, ta, oneMinusM,
    invOneMinusM, uLeft, uRight0, uRight, u⟩

/-- Boolean side conditions for the shared DAG. -/
def CommonData.safe (d : CommonData) : Bool :=
  nonneg d.input && nonneg d.r2 && expSafe 12 d.negR &&
  expSafe 12 d.mExponent && nonneg d.mRatio && nonneg d.m &&
  expSafe 12 d.aInner && positive d.onePlusR && nonneg d.aExp &&
  nonneg d.invOnePlusR && nonneg d.aRatio && nonneg d.a &&
  qtSafe 16 d.m && qtSafe 16 d.a && nonneg d.tm && nonneg d.ta &&
  positive d.oneMinusM && nonneg d.invOneMinusM && nonneg d.uLeft &&
  nonneg d.uRight0 && nonneg d.uRight && nonneg d.u

/-- Propositional decoding of the shared Boolean conditions. -/
structure CommonData.Checks (d : CommonData) : Prop where
  inputNonneg : nonneg d.input = true
  r2Nonneg : nonneg d.r2 = true
  expNegRSafe : expSafe 12 d.negR = true
  mExpSafe : expSafe 12 d.mExponent = true
  mRatioNonneg : nonneg d.mRatio = true
  mNonneg : nonneg d.m = true
  aExpSafe : expSafe 12 d.aInner = true
  onePlusRPositive : positive d.onePlusR = true
  aExpNonneg : nonneg d.aExp = true
  invOnePlusRNonneg : nonneg d.invOnePlusR = true
  aRatioNonneg : nonneg d.aRatio = true
  aNonneg : nonneg d.a = true
  mTaylorSafe : qtSafe 16 d.m = true
  aTaylorSafe : qtSafe 16 d.a = true
  tmNonneg : nonneg d.tm = true
  taNonneg : nonneg d.ta = true
  oneMinusMPositive : positive d.oneMinusM = true
  invOneMinusMNonneg : nonneg d.invOneMinusM = true
  uLeftNonneg : nonneg d.uLeft = true
  uRight0Nonneg : nonneg d.uRight0 = true
  uRightNonneg : nonneg d.uRight = true
  uNonneg : nonneg d.u = true

theorem CommonData.checks_of_safe {d : CommonData} (h : d.safe = true) : d.Checks := by
  simp only [CommonData.safe, Bool.and_eq_true] at h
  constructor <;> aesop

/-- Definitional equations of the shared DAG, packaged without unfolding its
fixed-point implementations during later proofs. -/
structure CommonData.WellFormed (d : CommonData) : Prop where
  r2 : d.r2 = mulNonneg d.input d.input
  r3 : d.r3 = mulNonneg d.r2 d.input
  remainder : d.remainder =
    add (add (add (rationalInterval (-1) 4)
      (mul (rationalInterval 31 100) d.input))
      (mul (rationalInterval 21 100) d.r2))
      (mul (rationalInterval (-2) 25) d.r3)
  negR : d.negR = neg d.input
  expNegR : d.expNegR = exp 12 d.negR
  mExponent : d.mExponent = add (mul (rationalInterval (-7) 10) d.input)
    (mul (rationalInterval (-13) 50) d.r2)
  mRatio : d.mRatio = exp 12 d.mExponent
  m : d.m = mulNonneg d.input d.mRatio
  aInner : d.aInner = neg (mul d.expNegR d.remainder)
  aExp : d.aExp = exp 12 d.aInner
  onePlusR : d.onePlusR = add (point scale) d.input
  invOnePlusR : d.invOnePlusR = inv d.onePlusR
  aRatio : d.aRatio = mulNonneg d.aExp d.invOnePlusR
  a : d.a = mulNonneg d.input d.aRatio
  tm : d.tm = t 16 d.m
  ta : d.ta = t 16 d.a
  oneMinusM : d.oneMinusM = sub (point scale) d.m
  invOneMinusM : d.invOneMinusM = inv d.oneMinusM
  uLeft : d.uLeft = mulNonneg d.mRatio d.tm
  uRight0 : d.uRight0 = mulNonneg d.aRatio d.ta
  uRight : d.uRight = mulNonneg d.uRight0 d.invOneMinusM
  u : d.u = add d.uLeft d.uRight

theorem commonData_wellFormed (I : Interval) : (commonData I).WellFormed := by
  constructor <;> rfl

/-- Real-semantic soundness of the shared DAG. -/
structure CommonData.Sound (d : CommonData) (r : ℝ) : Prop where
  r2 : d.r2.Contains (r ^ 2)
  expNegR : d.expNegR.Contains (Real.exp (-r))
  mRatio : d.mRatio.Contains (finalMRatio r)
  m : d.m.Contains (finalM r)
  aRatio : d.aRatio.Contains (finalARatio r)
  a : d.a.Contains (finalA r)
  u : d.u.Contains (finalU r)

theorem CommonData.sound {d : CommonData} {r : ℝ}
    (hw : d.WellFormed) (hc : d.Checks) (hr : d.input.Contains r)
    (hrpos : 0 < r) : d.Sound r := by
  have hInputNonneg : 0 ≤ d.input.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.inputNonneg
  have hR2Nonneg : 0 ≤ d.r2.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.r2Nonneg
  have hMRatioNonneg : 0 ≤ d.mRatio.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.mRatioNonneg
  have hAExpNonneg : 0 ≤ d.aExp.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.aExpNonneg
  have hInvOnePlusRNonneg : 0 ≤ d.invOnePlusR.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.invOnePlusRNonneg
  have hARatioNonneg : 0 ≤ d.aRatio.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.aRatioNonneg
  have hTmNonneg : 0 ≤ d.tm.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.tmNonneg
  have hTaNonneg : 0 ≤ d.ta.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.taNonneg
  have hInvOneMinusMNonneg : 0 ≤ d.invOneMinusM.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.invOneMinusMNonneg
  have hURight0Nonneg : 0 ≤ d.uRight0.lo := by
    simpa only [nonneg, decide_eq_true_eq] using hc.uRight0Nonneg
  have hOnePlusRPositive : 0 < d.onePlusR.lo := by
    simpa only [positive, decide_eq_true_eq] using hc.onePlusRPositive
  have hOneMinusMPositive : 0 < d.oneMinusM.lo := by
    simpa only [positive, decide_eq_true_eq] using hc.oneMinusMPositive
  have hone : (point scale).Contains (1 : ℝ) := by
    have h := Interval.contains_point scale
    convert h using 1
    norm_num [FixedPointInterval.value, scale]
  have hr2 : d.r2.Contains (r ^ 2) := by
    rw [hw.r2]
    simpa only [pow_two] using hr.mulNonneg hr hInputNonneg hInputNonneg
  have hr3 : d.r3.Contains (r ^ 3) := by
    rw [hw.r3]
    have h := hr2.mulNonneg hr hR2Nonneg hInputNonneg
    convert h using 1 <;> ring
  have hrem : d.remainder.Contains (finalRemainder r) := by
    have hq : (rationalInterval (-1) 4).Contains (-(1 / 4 : ℝ)) := by
      convert rationalInterval_contains (-1) (q := 4) (by norm_num) using 1 <;>
        norm_num
    have h31 : (rationalInterval 31 100).Contains (31 / 100 : ℝ) :=
      rationalInterval_contains 31 (q := 100) (by norm_num)
    have h21 : (rationalInterval 21 100).Contains (21 / 100 : ℝ) :=
      rationalInterval_contains 21 (q := 100) (by norm_num)
    have hn2 : (rationalInterval (-2) 25).Contains (-(2 / 25 : ℝ)) := by
      convert rationalInterval_contains (-2) (q := 25) (by norm_num) using 1 <;>
        norm_num
    rw [hw.remainder]
    have h := ((hq.add (h31.mul hr)).add (h21.mul hr2)).add (hn2.mul hr3)
    convert h using 1 <;> simp only [finalRemainder] <;> ring
  have hnegR : d.negR.Contains (-r) := by
    rw [hw.negR]
    exact hr.neg
  have hexpNegR : d.expNegR.Contains (Real.exp (-r)) := by
    rw [hw.expNegR]
    exact FixedPointInterval.Sound.contains_exp_of_safe hnegR hc.expNegRSafe
  have hmExponent : d.mExponent.Contains
      (-(7 / 10 : ℝ) * r - (13 / 50 : ℝ) * r ^ 2) := by
    have hn7 : (rationalInterval (-7) 10).Contains (-(7 / 10 : ℝ)) := by
      convert rationalInterval_contains (-7) (q := 10) (by norm_num) using 1 <;>
        norm_num
    have hn13 : (rationalInterval (-13) 50).Contains (-(13 / 50 : ℝ)) := by
      convert rationalInterval_contains (-13) (q := 50) (by norm_num) using 1 <;>
        norm_num
    rw [hw.mExponent]
    convert (hn7.mul hr).add (hn13.mul hr2) using 1 <;> ring
  have hmRatio : d.mRatio.Contains (finalMRatio r) := by
    rw [hw.mRatio]
    simpa only [finalMRatio] using
      (FixedPointInterval.Sound.contains_exp_of_safe hmExponent hc.mExpSafe)
  have hm : d.m.Contains (finalM r) := by
    rw [hw.m]
    simpa only [finalM_eq_mul_ratio] using
      hr.mulNonneg hmRatio hInputNonneg hMRatioNonneg
  have haInner : d.aInner.Contains
      (-Real.exp (-r) * finalRemainder r) := by
    rw [hw.aInner]
    convert (hexpNegR.mul hrem).neg using 1 <;> ring
  have haExp : d.aExp.Contains
      (Real.exp (-Real.exp (-r) * finalRemainder r)) := by
    rw [hw.aExp]
    exact FixedPointInterval.Sound.contains_exp_of_safe haInner hc.aExpSafe
  have hOnePlusR : d.onePlusR.Contains (1 + r) := by
    rw [hw.onePlusR]
    exact hone.add hr
  have hInvOnePlusR : d.invOnePlusR.Contains (1 + r)⁻¹ := by
    rw [hw.invOnePlusR]
    exact hOnePlusR.inv hOnePlusRPositive
  have haRatio : d.aRatio.Contains (finalARatio r) := by
    rw [hw.aRatio]
    simpa only [finalARatio, div_eq_mul_inv] using
      haExp.mulNonneg hInvOnePlusR hAExpNonneg hInvOnePlusRNonneg
  have ha : d.a.Contains (finalA r) := by
    rw [hw.a]
    rw [finalA_eq_mul_ratio hrpos]
    exact hr.mulNonneg haRatio hInputNonneg hARatioNonneg
  have htm : d.tm.Contains
      (CertifiedNumerics.negLogOneSubRatio (finalM r)) := by
    rw [hw.tm]
    exact FixedPointInterval.Sound.contains_t_of_safe hm hc.mTaylorSafe
  have hta : d.ta.Contains
      (CertifiedNumerics.negLogOneSubRatio (finalA r)) := by
    rw [hw.ta]
    exact FixedPointInterval.Sound.contains_t_of_safe ha hc.aTaylorSafe
  have hOneMinusM : d.oneMinusM.Contains (1 - finalM r) := by
    rw [hw.oneMinusM]
    simpa only [sub, sub_eq_add_neg] using hone.add hm.neg
  have hInvOneMinusM : d.invOneMinusM.Contains (1 - finalM r)⁻¹ := by
    rw [hw.invOneMinusM]
    exact hOneMinusM.inv hOneMinusMPositive
  have huLeft : d.uLeft.Contains
      (finalMRatio r * CertifiedNumerics.negLogOneSubRatio (finalM r)) := by
    rw [hw.uLeft]
    exact hmRatio.mulNonneg htm hMRatioNonneg hTmNonneg
  have huRight0 : d.uRight0.Contains
      (finalARatio r * CertifiedNumerics.negLogOneSubRatio (finalA r)) := by
    rw [hw.uRight0]
    exact haRatio.mulNonneg hta hARatioNonneg hTaNonneg
  have huRight : d.uRight.Contains
      (finalARatio r * CertifiedNumerics.negLogOneSubRatio (finalA r) /
        (1 - finalM r)) := by
    rw [hw.uRight]
    simpa only [div_eq_mul_inv] using
      huRight0.mulNonneg hInvOneMinusM hURight0Nonneg hInvOneMinusMNonneg
  have hu : d.u.Contains (finalU r) := by
    rw [hw.u]
    simpa only [finalU] using huLeft.add huRight
  exact ⟨hr2, hexpNegR, hmRatio, hm, haRatio, ha, hu⟩

end

end RamseyLean.FinalCertificate
